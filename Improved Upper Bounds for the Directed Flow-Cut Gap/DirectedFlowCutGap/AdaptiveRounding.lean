import DirectedFlowCutGap.AdaptiveEpoch
import DirectedFlowCutGap.FiniteCutLaw
import Mathlib.Data.Fin.Tuple.Take

/-!
# Finite sampling for the actual adaptive rounding schedule

The sampling space consists of a genuinely uniform permutation and independent
actual level-cut outcomes. Its finite law is proved to be the pushforward of
the real frozen experiment. Real-valued optimizer states are never assumed
finite. Runtime of the noncomputable optimizer choices is a separate issue.
-/
namespace DirectedFlowCutGap.AdaptiveRounding
noncomputable section
open MeasureTheory Set
open scoped BigOperators NNReal ENNReal
open CandidateSchedule CandidateSchedule.State AdaptiveEpoch
attribute [local instance] Classical.propDecidable

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

local instance permutationMeasurableSpace : MeasurableSpace (Equiv.Perm E) := ⊤

/-- Finite random input: one permutation and one cut outcome for each label. -/
abbrev Sample (E V : Type*) := Equiv.Perm E × (E → FiniteCutLaw.Outcome V)

/-- The permutation is uniform and independent of the independent actual cut laws. -/
def sampleMeasure (G : Digraph V) (w : E → V → ℝ≥0) (s : E → V) :
    Measure (Sample E V) :=
  (FrozenEpochProbability.finiteUniform (Equiv.Perm E)).prod
    (Measure.pi fun e => FiniteCutLaw.cutMeasure G (w e) (s e))

instance sampleMeasure_probability (G : Digraph V) (w : E → V → ℝ≥0) (s : E → V) :
    IsProbabilityMeasure (sampleMeasure G w s) := by
  unfold sampleMeasure
  infer_instance

/-- The finite law used for adaptive bind. -/
def samplePMF (G : Digraph V) (w : E → V → ℝ≥0) (s : E → V) : PMF (Sample E V) :=
  (sampleMeasure G w s).toPMF

@[simp] theorem samplePMF_toMeasure (G : Digraph V) (w : E → V → ℝ≥0) (s : E → V) :
    (samplePMF G w s).toMeasure = sampleMeasure G w s := Measure.toPMF_toMeasure _

/-- Coordinatewise application of the actual level cuts. -/
def drawSample (G : Digraph V) (w : E → V → ℝ≥0) (s : E → V)
    (ω : Equiv.Perm E × (E → ℝ)) : Sample E V :=
  (ω.1, fun e => FiniteCutLaw.draw G (w e) (s e) (ω.2 e))

omit [Fintype E] [DecidableEq E] in
theorem measurable_drawSample (G : Digraph V) (w : E → V → ℝ≥0) (s : E → V) :
    Measurable (drawSample G w s) := by
  exact measurable_fst.prodMk (Measurable.of_eval fun e =>
    (FiniteCutLaw.measurable_draw G (w e) (s e)).comp ((measurable_pi_apply e).comp measurable_snd))

/-- Exact product/pushforward bridge; independence is derived from the real law. -/
theorem sampleMeasure_eq_map (G : Digraph V) (w : E → V → ℝ≥0) (s : E → V) :
    sampleMeasure G w s = (FrozenEpochProbability.experiment E).map (drawSample G w s) := by
  have hpi : (FrozenEpochProbability.levelsMeasure E).map
      (fun d e => FiniteCutLaw.draw G (w e) (s e) (d e)) =
      Measure.pi (fun e => FiniteCutLaw.cutMeasure G (w e) (s e)) := by
    exact Measure.pi_map_pi (fun e => (FiniteCutLaw.measurable_draw G (w e) (s e)).aemeasurable)
  unfold sampleMeasure FrozenEpochProbability.experiment
  rw [← hpi]
  have hm : Measurable (fun d : E → ℝ => fun e => FiniteCutLaw.draw G (w e) (s e) (d e)) :=
    Measurable.of_eval fun e => (FiniteCutLaw.measurable_draw G (w e) (s e)).comp (measurable_pi_apply e)
  change _ = Measure.map (Prod.map id (fun d : E → ℝ => fun e => FiniteCutLaw.draw G (w e) (s e) (d e))) _
  rw [← Measure.map_prod_map _ _ measurable_id hm, Measure.map_id]


/-- Exact finite atom probabilities, displaying both independence factors. -/
theorem samplePMF_apply (G : Digraph V) (w : E → V → ℝ≥0) (s : E → V)
    (ω : Sample E V) : samplePMF G w s ω =
      (Fintype.card (Equiv.Perm E) : ℝ≥0∞)⁻¹ * ∏ e, FiniteCutLaw.cutPMF G (w e) (s e) (ω.2 e) := by
  rw [samplePMF, Measure.toPMF_apply]
  change (FrozenEpochProbability.finiteUniform (Equiv.Perm E)).prod
    (Measure.pi fun e => FiniteCutLaw.cutMeasure G (w e) (s e)) {(ω.1, ω.2)} = _
  rw [← singleton_prod_singleton, Measure.prod_prod, FrozenEpochProbability.finiteUniform_singleton,
    Measure.pi_singleton]
  rfl

/-- Every coordinate of a supported joint sample is a supported actual cut. -/
theorem sample_support_coordinate (G : Digraph V) (w : E → V → ℝ≥0) (s : E → V)
    {ω : Sample E V} (hω : ω ∈ (samplePMF G w s).support) (e : E) :
    ω.2 e ∈ (FiniteCutLaw.cutPMF G (w e) (s e)).support := by
  have hn : samplePMF G w s ω ≠ 0 := hω
  rw [samplePMF_apply] at hn
  exact (Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).2) e (Finset.mem_univ e)

/-- Finite expectations exactly equal their real-experiment counterparts. -/
theorem sample_expectation_eq_integral (G : Digraph V) (w : E → V → ℝ≥0) (s : E → V)
    (f : Sample E V → ℝ) :
    (∑ ω, (samplePMF G w s ω).toReal * f ω) =
      ∫ ω, f (drawSample G w s ω) ∂FrozenEpochProbability.experiment E := by
  calc
    _ = ∫ ω, f ω ∂(samplePMF G w s).toMeasure := by
      simpa only [smul_eq_mul] using (PMF.integral_eq_sum (samplePMF G w s) f).symm
    _ = _ := by
      rw [samplePMF_toMeasure, sampleMeasure_eq_map]
      exact integral_map (measurable_drawSample G w s).aemeasurable
        (measurable_of_finite f).aestronglyMeasurable

/-- Event probabilities also transfer exactly, before any stopping-time argument. -/
theorem sample_probability_eq (G : Digraph V) (w : E → V → ℝ≥0) (s : E → V)
    (A : Set (Sample E V)) :
    (samplePMF G w s).toMeasure A =
      FrozenEpochProbability.experiment E ((drawSample G w s) ⁻¹' A) := by
  rw [samplePMF_toMeasure, sampleMeasure_eq_map]
  exact Measure.map_apply (measurable_drawSample G w s) ((Set.toFinite A).measurableSet)

/-- The frozen virtual union can be evaluated directly on the finite cut outcomes. -/
def virtualCut (X : Finset V) (A : Finset E) (ω : Sample E V) : Finset V :=
  X ∪ (A.image ω.1).biUnion (fun e => (ω.2 e).cut)

omit [Fintype E] in
@[simp] theorem virtualCut_drawSample (G : Digraph V) (w : E → V → ℝ≥0)
    (s : E → V) (X : Finset V) (A : Finset E) (ω : Equiv.Perm E × (E → ℝ)) :
    virtualCut X A (drawSample G w s ω) =
      FrozenEpochProbability.frozenCut G w s X (A.image ω.1) ω.2 := rfl

/-- The previously proved unconditional prefix expectation transfers exactly
onto the finite sampling law. -/
theorem expected_virtual_new_card_le (G : Digraph V) (w : E → V → ℝ≥0)
    (s : E → V) (X : Finset V) (A : Finset E) :
    (∑ ω, samplePMF G w s ω * ((virtualCut X A ω \ X).card : ℝ≥0∞)) ≤
      (((A.card : ℝ≥0) / (Fintype.card E : ℝ≥0) *
        ∑ e, FrozenEpochProbability.outsideMass X (w e) : ℝ≥0) : ℝ≥0∞) := by
  have hm : Measurable (fun ω : Sample E V => ((virtualCut X A ω \ X).card : ℝ≥0∞)) :=
    measurable_of_finite _
  have he : (∑ ω, samplePMF G w s ω * ((virtualCut X A ω \ X).card : ℝ≥0∞)) =
      ∫⁻ ω, ((virtualCut X A ω \ X).card : ℝ≥0∞) ∂(samplePMF G w s).toMeasure := by
    rw [lintegral_fintype]
    simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), mul_comm]
  rw [he, samplePMF_toMeasure, sampleMeasure_eq_map,
    lintegral_map hm (measurable_drawSample G w s)]
  exact FrozenEpochProbability.lintegral_experiment_new_card_le G w s X A

/-- The genuine uniform-permutation survival bound on finite cut samples. -/
theorem virtual_residualPath_le_exp (G : Digraph V) (w : E → V → ℝ≥0)
    (s : E → V) (X : Finset V) (A : Finset E) (u v : V) :
    ((samplePMF G w s).toMeasure {ω | LevelResidualPath G (virtualCut X A ω) u v}).toReal ≤
      Real.exp (-(A.card : ℝ) *
        (∑ e, (levelSeparationValue G (w e) (s e) u v).toReal) / (Fintype.card E : ℝ)) := by
  rw [sample_probability_eq]
  exact FrozenEpochProbability.experiment_residualPath_le_exp G w s X u v A

section StateSamples
variable {G : Digraph V} {D : Finset (V × V)} {L : ℝ≥0}

/-- Only currently remaining original demand labels are permuted. -/
abbrev Label (S : State G D L) := ↥S.remaining

/-- A fixed deterministic enumeration, followed by the sampled permutation. -/
def sampleOrder (S : State G D L) (π : Equiv.Perm (Label S)) : List (V × V) :=
  (List.ofFn fun i : Fin (Fintype.card (Label S)) =>
    ((π ((Fintype.equivFin (Label S)).symm i)).val))

omit [Fintype V] in
theorem sampleOrder_nodup (S : State G D L) (π : Equiv.Perm (Label S)) :
    (sampleOrder S π).Nodup := by
  apply List.nodup_ofFn.mpr
  exact Subtype.val_injective.comp (π.injective.comp (Fintype.equivFin (Label S)).symm.injective)

omit [Fintype V] in
theorem sampleOrder_toFinset (S : State G D L) (π : Equiv.Perm (Label S)) :
    (sampleOrder S π).toFinset = S.remaining := by
  ext p
  simp only [sampleOrder, List.mem_toFinset, List.mem_ofFn]
  constructor
  · rintro ⟨i, rfl⟩
    exact (π ((Fintype.equivFin (Label S)).symm i)).property
  · intro hp
    refine ⟨(Fintype.equivFin (Label S)) (π.symm ⟨p, hp⟩), ?_⟩
    simp

/-- Supported cuts have genuine unit-level representatives; unused labels get zero. -/
def sampleLevels (S : State G D L) (ω : Sample (Label S) V) : (V × V) → UnitLevel :=
  fun p => if hp : p ∈ S.remaining then
    ⟨FiniteCutLaw.realizeLevel G (S.weight p) p.1 (ω.2 ⟨p, hp⟩),
      FiniteCutLaw.realizeLevel_le_one G (S.weight p) p.1 (ω.2 ⟨p, hp⟩)⟩
    else ⟨0, zero_le⟩

/-- A supported representative reproduces its cut outcome exactly; no claim
about the distribution of representative levels is made or needed. -/
theorem sampleLevels_cut (S : State G D L) {ω : Sample (Label S) V}
    (hω : ω ∈ (samplePMF G (fun p : Label S => S.weight p.val) (fun p => p.val.1)).support)
    (p : Label S) :
    levelCut G (S.weight p.val) p.val.1 (sampleLevels S ω p.val).val = (ω.2 p).cut := by
  simp only [sampleLevels, dite_eq_left p.property]
  exact FiniteCutLaw.realizeLevel_cut G (S.weight p.val) p.val.1
    (sample_support_coordinate G _ _ hω p)

/-- The finite set of the first `t` prescribed positions, before permutation. -/
def prefixSet (S : State G D L) (t : ℕ) (ht : t ≤ Fintype.card (Label S)) :
    Finset (Label S) :=
  FrozenEpochProbability.initialPrefix (Fintype.equivFin (Label S)).symm t ht

omit [Fintype V] in
theorem sampleOrder_take_toFinset (S : State G D L) (π : Equiv.Perm (Label S))
    (t : ℕ) (ht : t ≤ Fintype.card (Label S)) :
    ((sampleOrder S π).take t).toFinset = ((prefixSet S t ht).image π).image Subtype.val := by
  unfold sampleOrder
  rw [← Fin.ofFn_take_eq_take_ofFn ht]
  ext p
  simp [prefixSet, FrozenEpochProbability.initialPrefix, Fin.take]

/-- A deterministic horizon truncates the actual stopped scan. -/
def epochPrefix (r : ℝ≥0) (S : State G D L) (ω : Sample (Label S) V)
    (t : ℕ) : Result G D L :=
  run r S.mass (sampleLevels S ω) S ((sampleOrder S ω.1).take t)

/-- Both processes use exactly the same finite cut outcomes on the prefix. -/
theorem prefix_virtual_eq (S : State G D L) {ω : Sample (Label S) V}
    (hω : ω ∈ (samplePMF G (fun p : Label S => S.weight p.val) (fun p => p.val.1)).support)
    (t : ℕ) (ht : t ≤ Fintype.card (Label S)) :
    S.cut ∪ ((sampleOrder S ω.1).take t).toFinset.biUnion
      (fun p => levelCut G (S.weight p) p.1 (sampleLevels S ω p).val) =
      virtualCut S.cut (prefixSet S t ht) ω := by
  rw [sampleOrder_take_toFinset S ω.1 t ht, Finset.image_biUnion]
  unfold virtualCut
  congr 1
  apply Finset.biUnion_congr rfl
  intro p hp
  exact sampleLevels_cut S hω p

/-- Unconditional truncation domination on all positive-probability samples. -/
theorem epochPrefix_cut_subset (r : ℝ≥0) (S : State G D L) {ω : Sample (Label S) V}
    (hω : ω ∈ (samplePMF G (fun p : Label S => S.weight p.val) (fun p => p.val.1)).support)
    (t : ℕ) (ht : t ≤ Fintype.card (Label S)) :
    (epochPrefix r S ω t).state.cut ⊆ virtualCut S.cut (prefixSet S t ht) ω := by
  rw [← prefix_virtual_eq S hω t ht]
  exact run_cut_subset_virtual r S.mass (sampleLevels S ω) S ((sampleOrder S ω.1).take t)

/-- An active prefix has reached every one of its positions, so its actual cut
agrees with the virtual union. This is a joint-event coupling, not conditioning. -/
theorem epochPrefix_cut_eq_of_active (r : ℝ≥0) (S : State G D L)
    {ω : Sample (Label S) V}
    (hω : ω ∈ (samplePMF G (fun p : Label S => S.weight p.val) (fun p => p.val.1)).support)
    (t : ℕ) (ht : t ≤ Fintype.card (Label S))
    (hactive : Active r S.mass (epochPrefix r S ω t).state) :
    (epochPrefix r S ω t).state.cut = virtualCut S.cut (prefixSet S t ht) ω := by
  rw [← prefix_virtual_eq S hω t ht]
  apply run_cut_eq_virtual_of_full
  apply run_rounds_eq_length_of_active _ _ _ _ _ _ ((sampleOrder_nodup S ω.1).take) hactive
  intro p hp
  rw [← sampleOrder_toFinset S ω.1]
  exact List.mem_toFinset.mpr (List.mem_of_mem_take (List.mem_toFinset.mp hp))

/-- The finite subtype sum is the actual epoch-start mass. -/
theorem label_mass_sum (S : State G D L) :
    (∑ p : Label S, FrozenEpochProbability.outsideMass S.cut (S.weight p.val)) = S.mass := by
  simp only [FrozenEpochProbability.outsideMass, State.mass, EpochAccounting.familyMass,
    CandidateOptimization.outsideMass, Finset.sdiff_eq_filter]
  exact Finset.sum_attach S.remaining (fun p => ∑ v ∈ Finset.univ.filter (fun v => v ∉ S.cut), S.weight p v)

/-- Truncated epoch cost is bounded unconditionally; no conditioning on a good
event or on reaching the horizon appears in this expectation. -/
theorem expected_epochPrefix_new_card_le (r : ℝ≥0) (S : State G D L)
    (t : ℕ) (ht : t ≤ Fintype.card (Label S)) :
    (∑ ω, samplePMF G (fun p : Label S => S.weight p.val) (fun p => p.val.1) ω *
      (((epochPrefix r S ω t).state.cut \ S.cut).card : ℝ≥0∞)) ≤
      (((t : ℝ≥0) / (S.remaining.card : ℝ≥0) * S.mass : ℝ≥0) : ℝ≥0∞) := by
  calc
    _ ≤ ∑ ω, samplePMF G (fun p : Label S => S.weight p.val) (fun p => p.val.1) ω *
        ((virtualCut S.cut (prefixSet S t ht) ω \ S.cut).card : ℝ≥0∞) := by
      apply Finset.sum_le_sum
      intro ω hω
      by_cases hz : samplePMF G (fun p : Label S => S.weight p.val) (fun p => p.val.1) ω = 0
      · simp [hz]
      · apply mul_le_mul' le_rfl
        exact_mod_cast Finset.card_le_card (Finset.sdiff_subset_sdiff_left S.cut
          (epochPrefix_cut_subset r S hz t ht))
    _ ≤ _ := by
      have h := expected_virtual_new_card_le G
        (fun p : Label S => S.weight p.val) (fun p => p.val.1) S.cut (prefixSet S t ht)
      rw [label_mass_sum] at h
      simpa only [prefixSet, FrozenEpochProbability.initialPrefix_card, Fintype.card_coe] using h

/-- One actual bounded epoch for each finite random input. -/
def epoch (r : ℝ≥0) (S : State G D L) (ω : Sample (Label S) V) : Result G D L :=
  run r S.mass (sampleLevels S ω) S (sampleOrder S ω.1)

/-- The actual finite law of one epoch, on unrestricted real-valued states. -/
def epochPMF (r : ℝ≥0) (S : State G D L) : PMF (Result G D L) :=
  (samplePMF G (fun p : Label S => S.weight p.val) (fun p => p.val.1)).map (epoch r S)

theorem epoch_stopped (r : ℝ≥0) (S : State G D L) (ω : Sample (Label S) V) :
    ¬Active r S.mass (epoch r S ω).state :=
  run_stopped r S.mass (sampleLevels S ω) S (sampleOrder S ω.1)
    (sampleOrder_nodup S ω.1) (sampleOrder_toFinset S ω.1)

theorem epoch_progress (r : ℝ≥0) (hr : 1 ≤ r) (S : State G D L)
    (hready : S.Ready r) (hpos : S.optimum ≠ 0) (ω : Sample (Label S) V) :
    (epoch r S ω).state.remaining.card < S.remaining.card :=
  run_remaining_card_lt r hr (sampleLevels S ω) S (sampleOrder S ω.1)
    (sampleOrder_toFinset S ω.1) hready hpos

/-- Fuel is the initial number of labels. Every nonterminal epoch uses at least
one label, so this recursion is finite for every sample sequence. -/
def solve (r : ℝ≥0) (hr : 1 < r) : ℕ → State G D L → PMF (State G D L)
  | 0, S => PMF.pure (S.stabilize r hr)
  | fuel + 1, S =>
      let T := S.stabilize r hr
      if T.optimum = 0 then PMF.pure T else
        (samplePMF G (fun p : Label T => T.weight p.val) (fun p => p.val.1)).bind
          (fun ω => solve r hr fuel (epoch r T ω).state)

/-- Every supported output is connected to the input by an actual finite
optimizer-and-level-cut trace, with no oracle transition. -/
theorem solve_support_execution (r : ℝ≥0) (hr : 1 < r) (fuel : ℕ)
    (S : State G D L) {T : State G D L} (hT : T ∈ (solve r hr fuel S).support) :
    ∃ k q, Execution r S k q T := by
  induction fuel generalizing S with
  | zero =>
      have he : T = S.stabilize r hr := by simpa [solve] using hT
      subst T
      refine ⟨S.restartCount r hr, 0, ?_⟩
      simpa [State.stabilize] using
        (Execution.stabilize_prefix (Execution.start (S₀ := S)) hr (j := S.restartCount r hr) le_rfl)
  | succ fuel ih =>
      simp only [solve] at hT
      split_ifs at hT with hz
      · have he : T = S.stabilize r hr := by simpa using hT
        subst T
        refine ⟨S.restartCount r hr, 0, ?_⟩
        simpa [State.stabilize] using
          (Execution.stabilize_prefix (Execution.start (S₀ := S)) hr (j := S.restartCount r hr) le_rfl)
      · obtain ⟨ω, hω, ht⟩ := (PMF.mem_support_bind_iff _ _ _).mp hT
        obtain ⟨k, q, hrun⟩ := ih _ ht
        have hstab : Execution r S (S.restartCount r hr) 0 (S.stabilize r hr) := by
          simpa [State.stabilize] using Execution.stabilize_prefix
            (Execution.start (S₀ := S)) hr (j := S.restartCount r hr) le_rfl
        have hepoch := run_execution r (S.stabilize r hr).mass
          (sampleLevels (S.stabilize r hr) ω) (sampleOrder (S.stabilize r hr) ω.1) hstab
        exact ⟨_, _, execution_trans r hepoch hrun⟩

/-- With the proved label-count fuel, every run terminates at zero optimum. -/
theorem solve_support_zero (r : ℝ≥0) (hr : 1 < r) (fuel : ℕ)
    (S : State G D L) (hfuel : S.remaining.card ≤ fuel)
    {T : State G D L} (hT : T ∈ (solve r hr fuel S).support) : T.optimum = 0 := by
  induction fuel generalizing S with
  | zero =>
      have he : T = S.stabilize r hr := by simpa [solve] using hT
      subst T
      apply optimum_eq_zero_of_remaining_empty
      rw [stabilize_remaining]
      exact Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hfuel)
  | succ fuel ih =>
      simp only [solve] at hT
      split_ifs at hT with hz
      · have he : T = S.stabilize r hr := by simpa using hT
        simpa only [he] using hz
      · obtain ⟨ω, hω, ht⟩ := (PMF.mem_support_bind_iff _ _ _).mp hT
        apply ih _ _ ht
        have hprogress := epoch_progress r hr.le (S.stabilize r hr)
          (S.stabilize_ready r hr) hz ω
        rw [stabilize_remaining] at hprogress
        omega

/-- Geometric mass fuel is a second, sharper termination proof. The base case
uses the actual unit lower bound on any unresolved fractional cut. -/
theorem solve_support_zero_of_mass_fuel (r : ℝ≥0) (hr : 1 < r) (fuel : ℕ)
    (S : State G D L) (hfuel : (S.stabilize r hr).mass < r ^ fuel)
    {T : State G D L} (hT : T ∈ (solve r hr fuel S).support) : T.optimum = 0 := by
  induction fuel generalizing S with
  | zero =>
      have he : T = S.stabilize r hr := by simpa [solve] using hT
      subst T
      by_contra hpos
      have hlo := (S.stabilize r hr).one_le_optimum hpos
      have hm := (S.stabilize r hr).optimum_le_mass
      simpa using (not_lt_of_ge (hlo.trans hm)) hfuel
  | succ fuel ih =>
      simp only [solve] at hT
      split_ifs at hT with hz
      · have he : T = S.stabilize r hr := by simpa using hT
        simpa only [he] using hz
      · obtain ⟨ω, hω, ht⟩ := (PMF.mem_support_bind_iff _ _ _).mp hT
        let U := (epoch r (S.stabilize r hr) ω).state
        by_cases hnext : (U.stabilize r hr).optimum = 0
        · have ht' : T ∈ (solve r hr fuel U).support := ht
          have he : T = U.stabilize r hr := by
            cases fuel <;> simpa [solve, hnext] using ht'
          simpa only [he] using hnext
        · apply ih U _ ht
          have hdrop := next_start_mass r (S.stabilize r hr).mass hr U
            (run_mass_le r (S.stabilize r hr).mass (sampleLevels (S.stabilize r hr) ω) _ _)
            (epoch_stopped r (S.stabilize r hr) ω) hnext
          have hmul : r * (U.stabilize r hr).mass < r * r ^ fuel := by
            simpa only [pow_succ, mul_comm] using hdrop.trans_lt hfuel
          exact lt_of_mul_lt_mul_left hmul zero_le

/-- All supported outputs, including probabilistic failure events, are valid. -/
theorem solve_support_integralCut (r : ℝ≥0) (hr : 1 < r) (fuel : ℕ)
    (S : State G D L) (hfuel : S.remaining.card ≤ fuel)
    {T : State G D L} (hT : T ∈ (solve r hr fuel S).support) :
    IsIntegralCut G T.cut (D : Set (V × V)) :=
  T.integralCut_of_zero (solve_support_zero r hr fuel S hfuel hT)

/-- The cap bound counts real installations only, throughout all analysis epochs. -/
theorem solve_support_scale_le (r : ℝ≥0) (hr : 1 < r) (fuel : ℕ)
    (S : State G D L) {J : ℕ} (hJ : S.mass < r ^ (J + 1))
    {T : State G D L} (hT : T ∈ (solve r hr fuel S).support) :
    T.scale ≤ 4 ^ J * S.scale := by
  obtain ⟨k, q, h⟩ := solve_support_execution r hr fuel S hT
  exact h.scale_le hr hJ

/-- The returned finite cut law, with no optimizer-state finiteness requirement. -/
def outputPMF (r : ℝ≥0) (hr : 1 < r) (S : State G D L) : PMF (Finset V) :=
  (solve r hr S.remaining.card S).map State.cut

theorem outputPMF_valid (r : ℝ≥0) (hr : 1 < r) (S : State G D L)
    {X : Finset V} (hX : X ∈ (outputPMF r hr S).support) :
    IsIntegralCut G X (D : Set (V × V)) := by
  obtain ⟨T, hT, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hX
  exact solve_support_integralCut r hr _ S le_rfl hT

end StateSamples
end
end DirectedFlowCutGap.AdaptiveRounding
