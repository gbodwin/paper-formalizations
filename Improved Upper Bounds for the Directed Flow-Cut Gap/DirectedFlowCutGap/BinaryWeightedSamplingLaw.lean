import DirectedFlowCutGap.BinaryWeightedSampling

/-!
# Finite-ticket law of the actual binary weighted sampler

The output label is an arbitrary Boolean list. Probability is measured directly
by the PMF outer measure, so no finite-type instance for labels or retained
rational histories is required. Only the ticket domain is finite.

The ideal uniform-ticket specification has the exact retained-rational ratio.
The actual program consumes fair Boolean draws through the checked binary
sampler; exhaustion still returns its legal default and has an explicit error
term. Exact avoidance is proved for every supported result under any bit law,
including default and zero-total outcomes. This is a one-call probability
bridge. Adaptive oracle quality, its bad-history mass and the final global
runtime composition remain separate.
-/
namespace DirectedFlowCutGap.BinaryWeightedSamplingLaw
open BinaryArithmetic BinaryWeightedMasses BinaryWeightedSampling
open scoped BigOperators ENNReal

noncomputable section

variable {A : Type*}

/-- A specification only: execution never enumerates the ticket set. -/
def ticketLaw (xs : List (A × ℕ)) (h : 0 < IntegerWeightedChoice.total xs) :
    PMF (Option A) :=
  (PMF.uniformOfFinset Finset.univ
    (show (Finset.univ : Finset (Fin (IntegerWeightedChoice.total xs))).Nonempty
      from ⟨⟨0,h⟩,Finset.mem_univ _⟩)).map
        (fun u => IntegerWeightedChoice.choose xs u.val)

theorem ticket_count (xs : List (A × ℕ)) (pred : A → Bool) :
    (Finset.univ.filter fun u : Fin (IntegerWeightedChoice.total xs) =>
      (IntegerWeightedChoice.choose xs u.val).any pred = true).card =
        IntegerWeightedChoice.selectedMass xs pred := by
  classical
  rw [Finset.card_eq_sum_ones,Finset.sum_filter]
  exact (Fin.sum_univ_eq_sum_range
    (fun u => if (IntegerWeightedChoice.choose xs u).any pred = true then 1 else 0)
    (IntegerWeightedChoice.total xs)).trans
      (IntegerWeightedChoice.selection_count xs pred)

/-- Duplicate labels retain their combined mass, with literal label equality. -/
theorem ticketLaw_probability (xs : List (A × ℕ))
    (h : 0 < IntegerWeightedChoice.total xs) (pred : A → Bool) :
    ((ticketLaw xs h).toOuterMeasure {a | a.any pred = true}).toReal =
      (IntegerWeightedChoice.selectedMass xs pred : ℝ) /
        (IntegerWeightedChoice.total xs : ℝ) := by
  classical
  rw [ticketLaw,PMF.toOuterMeasure_map_apply,PMF.toOuterMeasure_uniformOfFinset_apply]
  simp only [Set.mem_preimage,Set.mem_ofPred_eq,ticket_count,
    Finset.card_univ,Fintype.card_fin,ENNReal.toReal_div,ENNReal.toReal_natCast]

theorem prepare_data (xs : Input) :
    data (prepare xs).masses = (RawWeightedMasses.encode (inputData xs)).2 := by
  exact congrArg Prod.snd (encode_refines xs)

theorem prepare_ratio (xs : Input) (pred : Bits → Bool) :
    (IntegerWeightedChoice.selectedMass (data (prepare xs).masses) pred : ℝ) /
        (value (prepare xs).total : ℝ) =
      RawWeightedMasses.selectedValue (inputData xs) pred /
        RawWeightedMasses.selectedValue (inputData xs) (fun _ => true) := by
  rw [(prepare xs).total_eq,prepare_data,RawWeightedMasses.encode_ratio]

theorem prepare_positive (xs : Input)
    (h : 0 < RawWeightedMasses.selectedValue (inputData xs) (fun _ => true)) :
    0 < value (prepare xs).total := by
  rw [(prepare xs).total_eq,prepare_data]
  exact RawWeightedMasses.encode_total_positive _ h

/-- Literal fair Boolean requests; numerical decoding is proof-side only. -/
def fairBit : PMF Bool :=
  (PMF.uniformOfFintype (Fin 2)).map (fun i => decide (i.val = 1))

theorem fairBit_index :
    BinaryRandomWord.bitIndex <$> fairBit = PMF.uniformOfFintype (Fin 2) := by
  change fairBit.map BinaryRandomWord.bitIndex = _
  rw [fairBit,PMF.map_comp]
  have h : (BinaryRandomWord.bitIndex ∘ fun i : Fin 2 => decide (i.val = 1)) = id := by
    funext i
    fin_cases i <;> rfl
  rw [h,PMF.map_id]

/-- Only reached two-way requests are interpreted; arbitrary finite callbacks
are absent from a binary tree. -/
theorem execute_binary_ideal {B : Type} {tree : FiniteDrawTrees.Tree B}
    (h : LazyFairBitTrees.Binary tree) :
    FiniteDrawTrees.execute (MonadicBitSampler.liftBit
      (PMF.uniformOfFintype (Fin 2))) tree = FiniteDrawTrees.ideal tree := by
  induction h with
  | pure a => rfl
  | draw h ih =>
      simp only [FiniteDrawTrees.execute,MonadicBitSampler.liftBit_two,
        FiniteDrawTrees.ideal,FiniteDrawTrees.law,FiniteDrawTrees.uniformDraw]
      congr 1
      funext a
      exact ih a

/-- The entire returned default record, including failure and counters, has
the lazy rejection law. This does not identify rejection with exact uniform. -/
theorem draw_observe_law (bound fuel : Bits) (positive : 0 < value bound) :
    BinaryBoundedSampler.observe <$>
      BinaryBoundedSampler.draw fairBit bound positive fuel =
        FiniteDrawTrees.ideal
          (LazyFairBitTrees.rejection (value bound) positive (value fuel)) := by
  rw [BinaryBoundedSampler.draw_refines,fairBit_index,MonadicBitSampler.draw_refines]
  exact execute_binary_ideal (LazyFairBitTrees.rejection_binary _ _ _)

theorem samplePrepared_label_law (p : Prepared) (fuel : Bits)
    (positive : 0 < value p.total) :
    (samplePrepared fairBit p fuel).map BinaryWeightedSampling.Result.label =
      (@BitSamplerCoupling.fallback (value p.total) (value fuel) ⟨positive.ne'⟩).map
        (fun u => IntegerWeightedChoice.choose (data p.masses) u.val) := by
  have hz : ¬ (isZero p.total).1 = true := by
    intro h
    have he := (isZero_spec p.total).1.mp h
    omega
  let select : Fin (value p.total) → Option Bits :=
    fun u => IntegerWeightedChoice.choose (data p.masses) u.val
  calc
    _ = (BinaryBoundedSampler.draw fairBit p.total positive fuel).map
        (fun r => select (BinaryBoundedSampler.observe r).value) := by
      change (fun r => r.label) <$> samplePrepared fairBit p fuel = _
      rw [samplePrepared_label]
      simp [BinaryBoundedSampler.checkedDrawCharged,hz,select,
        BinaryBoundedSampler.observe,bind_pure_comp,PMF.monad_map_eq_map,PMF.map_comp,Function.comp_def]
    _ = ((BinaryBoundedSampler.draw fairBit p.total positive fuel).map
        BinaryBoundedSampler.observe).map
          (fun r => select r.value) := by rw [PMF.map_comp]; rfl
    _ = (FiniteDrawTrees.ideal
        (LazyFairBitTrees.rejection (value p.total) positive (value fuel))).map
          (fun r => select r.value) := by
      exact congrArg (fun q : PMF (BitSamplerCoupling.DefaultOutput (value p.total)) =>
          q.map (fun r => select r.value))
        (draw_observe_law p.total fuel positive)
    _ = _ := by
      change (FiniteDrawTrees.ideal
        (LazyFairBitTrees.rejection (value p.total) positive (value fuel))).map
          (select ∘ BitSamplerCoupling.DefaultOutput.value) = _
      rw [← PMF.map_comp,LazyFairBitTrees.rejection_value_law]

/-- One actual call incurs only the proved bounded-rejection event error. -/
theorem samplePrepared_event_le (p : Prepared) (fuel : Bits)
    (positive : 0 < value p.total) (pred : Bits → Bool) :
    ((samplePrepared fairBit p fuel).toOuterMeasure
      {r | r.label.any pred = true}).toReal ≤
        (IntegerWeightedChoice.selectedMass (data p.masses) pred : ℝ) /
          (value p.total : ℝ) + ((1 : ℝ) / 2) ^ value fuel := by
  let : NeZero (value p.total) := ⟨positive.ne'⟩
  have h := BitSamplerCoupling.fallback_event_le (value p.total) (value fuel)
    (fun u => (IntegerWeightedChoice.choose (data p.masses) u.val).any pred = true)
  have hi := ticketLaw_probability (data p.masses)
    (by rw [← p.total_eq]; exact positive) pred
  have hu : FiniteAmplification.probability
      (PMF.uniformOfFintype (Fin (value p.total)))
      (fun u => (IntegerWeightedChoice.choose (data p.masses) u.val).any pred = true) =
        (IntegerWeightedChoice.selectedMass (data p.masses) pred : ℝ) /
          (value p.total : ℝ) := by
    have uniform_probability (N : ℕ)
        (hN : IntegerWeightedChoice.total (data p.masses) = N) [NeZero N] :
        FiniteAmplification.probability (PMF.uniformOfFintype (Fin N))
          (fun u => (IntegerWeightedChoice.choose (data p.masses) u.val).any pred = true) =
            (IntegerWeightedChoice.selectedMass (data p.masses) pred : ℝ) / (N : ℝ) := by
      subst N
      simpa only [ticketLaw,PMF.uniformOfFintype,PMF.toOuterMeasure_map_apply,
        FiniteAmplification.probability,Set.preimage_ofPred_eq] using hi
    exact uniform_probability (value p.total) p.total_eq.symm
  have he : ((samplePrepared fairBit p fuel).toOuterMeasure
        {r | r.label.any pred = true}).toReal =
      FiniteAmplification.probability
        (BitSamplerCoupling.fallback (value p.total) (value fuel))
        (fun u => (IntegerWeightedChoice.choose (data p.masses) u.val).any pred = true) := by
    calc
      _ = (((samplePrepared fairBit p fuel).map BinaryWeightedSampling.Result.label).toOuterMeasure
          {a | a.any pred = true}).toReal := by
        rw [PMF.toOuterMeasure_map_apply]
        rfl
      _ = _ := by
        rw [samplePrepared_label_law p fuel positive,PMF.toOuterMeasure_map_apply]
        rfl
  rw [he]
  exact h.trans_eq (congrArg (fun x : ℝ => x + ((1 : ℝ) / 2) ^ value fuel) hu)

theorem sample_event_le (xs : Input) (fuel : Bits)
    (positive : 0 < RawWeightedMasses.selectedValue (inputData xs) (fun _ => true))
    (pred : Bits → Bool) :
    ((sample fairBit xs fuel).toOuterMeasure {r | r.label.any pred = true}).toReal ≤
      RawWeightedMasses.selectedValue (inputData xs) pred /
        RawWeightedMasses.selectedValue (inputData xs) (fun _ => true) +
          ((1 : ℝ) / 2) ^ value fuel := by
  have h := samplePrepared_event_le (prepare xs) fuel (prepare_positive xs positive) pred
  rw [prepare_ratio] at h
  simpa only [sample,PMF.monad_map_eq_map,PMF.toOuterMeasure_map_apply,Set.preimage_ofPred_eq] using h

/-- Support exclusion is exact under any bit law, even on rejection exhaustion. -/
theorem finish_avoids (p : Prepared) (pred : Bits → Bool)
    (h : ∀ x ∈ p.masses, pred x.1 = false)
    (r : Option (BinaryBoundedSampler.Output p.total) × ℕ) :
    (finish p r).label.any pred = false := by
  rcases r with ⟨r,q⟩
  cases r with
  | none => rfl
  | some ticket =>
      obtain ⟨label,mass,hl,hm,_⟩ := finish_member p ticket q
      rw [hl]
      exact h (label,mass) hm

theorem samplePrepared_event_zero (bit : PMF Bool) (p : Prepared) (fuel : Bits)
    (pred : Bits → Bool) (h : ∀ x ∈ p.masses, pred x.1 = false) :
    (samplePrepared bit p fuel).toOuterMeasure {r | r.label.any pred = true} = 0 := by
  apply (PMF.toOuterMeasure_apply_eq_zero_iff _ _).mpr
  apply Set.disjoint_left.mpr
  intro r hr he
  obtain ⟨q,_hq,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hr
  have hn := finish_avoids p pred h q
  change (finish p q).label.any pred = true at he
  rw [hn] at he
  cases he

theorem prepare_avoids (xs : Input) (pred : Bits → Bool)
    (h : ∀ x ∈ xs, pred x.1 = false) :
    ∀ x ∈ (prepare xs).masses, pred x.1 = false := by
  intro x hx
  have hm : x.1 ∈ (encode xs).masses.map Prod.fst := List.mem_map.mpr ⟨x,hx,rfl⟩
  rw [encode_labels] at hm
  obtain ⟨y,hy,he⟩ := List.mem_map.mp hm
  simpa only [he] using h y hy

theorem sample_event_zero (bit : PMF Bool) (xs : Input) (fuel : Bits)
    (pred : Bits → Bool) (h : ∀ x ∈ xs, pred x.1 = false) :
    (sample bit xs fuel).toOuterMeasure {r | r.label.any pred = true} = 0 := by
  simpa only [sample,PMF.monad_map_eq_map,PMF.toOuterMeasure_map_apply,Set.preimage_ofPred_eq] using
    samplePrepared_event_zero bit (prepare xs) fuel pred (prepare_avoids xs pred h)

/-- Event conversion and cost-record updates preserve the actual returned
mask. The original event amount is the rational field in this ratio. -/
theorem sampleEvents_event_le {m : ℕ} (es : List (BinaryFractionalCore.Event m))
    (fuel : Bits) (pred : Bits → Bool)
    (positive : 0 < RawWeightedMasses.selectedValue
      (inputData (eventInput es).1) (fun _ => true)) :
    ((sampleEvents fairBit es fuel).toOuterMeasure {r | r.label.any pred = true}).toReal ≤
      RawWeightedMasses.selectedValue (inputData (eventInput es).1) pred /
        RawWeightedMasses.selectedValue (inputData (eventInput es).1) (fun _ => true) +
          ((1 : ℝ) / 2) ^ value fuel := by
  simpa only [sampleEvents,PMF.monad_map_eq_map,PMF.toOuterMeasure_map_apply,Set.preimage_ofPred_eq] using
    sample_event_le (eventInput es).1 fuel positive pred

theorem sampleEvents_event_zero {m : ℕ} (bit : PMF Bool)
    (es : List (BinaryFractionalCore.Event m)) (fuel : Bits) (pred : Bits → Bool)
    (h : ∀ e ∈ es, pred e.choice.mask.toList = false) :
    (sampleEvents bit es fuel).toOuterMeasure {r | r.label.any pred = true} = 0 := by
  have hi : ∀ x ∈ (eventInput es).1, pred x.1 = false := by
    rw [eventInput_value]
    intro x hx
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hx
    exact h e he
  simpa only [sampleEvents,PMF.monad_map_eq_map,PMF.toOuterMeasure_map_apply,Set.preimage_ofPred_eq] using
    sample_event_zero bit (eventInput es).1 fuel pred hi

end
end DirectedFlowCutGap.BinaryWeightedSamplingLaw
