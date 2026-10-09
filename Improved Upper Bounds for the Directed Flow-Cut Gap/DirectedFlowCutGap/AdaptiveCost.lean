import DirectedFlowCutGap.AdaptiveRounding
import DirectedFlowCutGap.EpochParameterBridge
import DirectedFlowCutGap.FiniteAmplification

/-!
# Quantitative analysis of actual adaptive epochs

This module connects the actual finite adaptive law to graph charging,
truncation, the fixed-pair survival theorem, and finite union bounds.
Candidate minima are always taken at their actual cap. Probability statements
are transferred through cut outcomes, never through representative levels.
-/
namespace DirectedFlowCutGap.AdaptiveCost
noncomputable section
open MeasureTheory Set
open scoped BigOperators NNReal ENNReal
open CandidateSchedule CandidateSchedule.State AdaptiveEpoch AdaptiveRounding
open EpochParameterBridge
attribute [local instance] Classical.propDecidable
local instance {A : Type*} : MeasurableSpace (Equiv.Perm A) := ⊤

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : Digraph V} {D : Finset (V × V)} {L : ℝ≥0}

/-- A legal prescribed ordering can be split at any fixed position. -/
theorem run_append_state (r M : ℝ≥0) (level : (V × V) → UnitLevel)
    (S : State G D L) (as bs : List (V × V))
    (hn : (as ++ bs).Nodup) (hsub : (as ++ bs).toFinset ⊆ S.remaining) :
    (run r M level S (as ++ bs)).state =
      (run r M level (run r M level S as).state bs).state := by
  induction as generalizing S with
  | nil => rfl
  | cons p ps ih =>
      have hp : p ∈ S.remaining := hsub (by simp)
      by_cases ha : Active r M S
      · have h : Active r M S ∧ p ∈ S.remaining := ⟨ha, hp⟩
        simp only [List.cons_append, run, dite_eq_left h]
        apply ih _ (List.nodup_cons.mp hn).2
        intro q hq
        apply Finset.mem_erase.mpr
        refine ⟨?_, hsub (by rw [List.cons_append, List.toFinset_cons]; exact Finset.mem_insert_of_mem hq)⟩
        intro he
        exact (List.nodup_cons.mp hn).1 (he ▸ List.mem_toFinset.mp hq)
      · rw [run_of_not_active r M level S (p :: ps ++ bs) ha,
          run_of_not_active r M level S (p :: ps) ha]
        exact (congrArg Result.state (run_of_not_active r M level S bs ha)).symm

/-- If the truncated scan has stopped, the rest of the sampled epoch is unused. -/
theorem epoch_eq_prefix_of_not_active (r : ℝ≥0) (S : State G D L)
    (ω : Sample (Label S) V) (t : ℕ)
    (hstop : ¬Active r S.mass (epochPrefix r S ω t).state) :
    (epoch r S ω).state = (epochPrefix r S ω t).state := by
  have he := run_append_state r S.mass (sampleLevels S ω) S
    ((sampleOrder S ω.1).take t) ((sampleOrder S ω.1).drop t)
    (by simpa using sampleOrder_nodup S ω.1)
    (by rw [List.take_append_drop, sampleOrder_toFinset])
  rw [List.take_append_drop] at he
  change (run r S.mass (sampleLevels S ω) S (sampleOrder S ω.1)).state = _
  rw [he]
  have hx := congrArg (fun R : Result G D L => R.state)
    (run_of_not_active r S.mass (sampleLevels S ω)
      (epochPrefix r S ω t).state ((sampleOrder S ω.1).drop t) hstop)
  exact hx

/-- Failure can cost at most the entire vertex set; every run still stays valid. -/
theorem epoch_new_card_le_prefix_add_failure (r : ℝ≥0) (S : State G D L)
    (ω : Sample (Label S) V) (t : ℕ) :
    ((epoch r S ω).state.cut \ S.cut).card ≤
      ((epochPrefix r S ω t).state.cut \ S.cut).card +
        if Active r S.mass (epochPrefix r S ω t).state then Fintype.card V else 0 := by
  by_cases ha : Active r S.mass (epochPrefix r S ω t).state
  · rw [ite_eq_left ha]
    have hc := Finset.card_le_univ ((epoch r S ω).state.cut \ S.cut)
    omega
  · rw [ite_eq_right ha, Nat.add_zero, epoch_eq_prefix_of_not_active r S ω t ha]

/-- At the full horizon a legal epoch is stopped, deterministically. -/
theorem epochPrefix_full_not_active (r : ℝ≥0) (S : State G D L)
    (ω : Sample (Label S) V) :
    ¬Active r S.mass (epochPrefix r S ω (Fintype.card (Label S))).state := by
  have hlen : (sampleOrder S ω.1).length = Fintype.card (Label S) := by simp [sampleOrder]
  simpa only [epoch, epochPrefix, ← hlen, List.take_length] using epoch_stopped r S ω

omit [Fintype V] in
/-- Exact conversion of the frozen label subtype sum. -/
theorem label_value_sum (S : State G D L) (u v : V) :
    (∑ p : Label S, (levelSeparationValue G (S.weight p.val) p.val.1 u v).toReal) =
      ∑ p ∈ S.remaining, (levelSeparationValue G (S.weight p) p.1 u v).toReal := by
  exact Finset.sum_attach S.remaining
    (fun p => (levelSeparationValue G (S.weight p) p.1 u v).toReal)

/-- The fixed epoch-start threshold supplied by every active current state. -/
def valueThreshold (r : ℝ≥0) (S : State G D L) (B : ℝ) : ℝ :=
  (S.mass : ℝ) * ((L : ℝ) / Fintype.card V) ^ (3 / 2 : ℝ) /
    ((r : ℝ) * graphDenominator (Fintype.card V) B r)

/-- Apply actual-cap charging first, then enlarge its numerical denominator;
current mass is only bounded below by the recorded start mass divided by `r`. -/
theorem active_prefix_value_witness [Nonempty V] (r : ℝ≥0) (hr : 1 < r)
    (S : State G D L) (B : ℝ) (hB : 1 ≤ S.scale) (hcap : (S.scale : ℝ) ≤ B)
    (hL : 64 * B ≤ (L : ℝ)) (hLn : (L : ℝ) ≤ Fintype.card V)
    (hnL : (Fintype.card V : ℝ) ≤ (L : ℝ) ^ 3)
    {ω : Sample (Label S) V}
    (hω : ω ∈ (samplePMF G (fun p : Label S => S.weight p.val) (fun p => p.val.1)).support)
    (t : ℕ) (ht : t ≤ Fintype.card (Label S))
    (ha : Active r S.mass (epochPrefix r S ω t).state) :
    ∃ u v, LevelResidualPath G (virtualCut S.cut (prefixSet S t ht) ω) u v ∧
      valueThreshold r S B ≤
        ∑ p : Label S, (levelSeparationValue G (S.weight p.val) p.val.1 u v).toReal := by
  let T := (epochPrefix r S ω t).state
  have hscale : T.scale = S.scale := run_scale r S.mass (sampleLevels S ω) S _
  have hBreal : (1 : ℝ) ≤ S.scale := by exact_mod_cast hB
  have hrreal : (1 : ℝ) < r := by exact_mod_cast hr
  have hK := graphDenominator_pos (Fintype.card V) (lt_of_lt_of_le zero_lt_one (hBreal.trans hcap))
    (lt_trans zero_lt_one hrreal)
  obtain ⟨u, v, hpath, hvalue⟩ := exists_state_graph_value T r
    (by simpa only [hscale] using hB)
    (by rw [hscale]; nlinarith) hr ha.1 ha.2.1 hLn hnL
  have hvalue' : (T.mass : ℝ) * ((L : ℝ) / Fintype.card V) ^ (3 / 2 : ℝ) /
      graphDenominator (Fintype.card V) B r ≤
      ∑ p ∈ T.remaining, (levelSeparationValue G (T.weight p) p.1 u v).toReal := by
    apply value_bound_of_cap_le _ (by simpa only [hscale] using hcap)
      (lt_trans zero_lt_one hrreal) (by positivity) hvalue
    rw [hscale]
    exact lt_of_lt_of_le zero_lt_one hBreal
  refine ⟨u, v, ?_, ?_⟩
  · rw [← epochPrefix_cut_eq_of_active r S hω t ht ha]
    exact hpath
  · rw [label_value_sum]
    apply le_trans _ (remaining_value_le r S.mass (sampleLevels S ω) S ((sampleOrder S ω.1).take t) u v)
    apply le_trans _ hvalue'
    have hm : (S.mass : ℝ) ≤ (r : ℝ) * T.mass := by exact_mod_cast ha.2.2
    unfold valueThreshold
    calc
      _ ≤ ((r : ℝ) * T.mass) * ((L : ℝ) / Fintype.card V) ^ (3 / 2 : ℝ) /
          ((r : ℝ) * graphDenominator (Fintype.card V) B r) := by
        apply div_le_div_of_nonneg_right _ (mul_pos (lt_trans zero_lt_one hrreal) hK).le
        exact mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg (by positivity) _)
      _ = _ := by field_simp

section UnionBound
variable {E : Type*} [Fintype E] [DecidableEq E]
local instance permutationMeasurableSpace : MeasurableSpace (Equiv.Perm E) := ⊤

/-- A union bound over all graph pairs converts fixed-pair virtual survival
into a bound for any supported event exhibiting a sufficiently valuable pair. -/
theorem valuable_pair_event_le (G : Digraph V) (w : E → V → ℝ≥0) (s : E → V)
    (X : Finset V) (A : Finset E) (a : ℝ) (bad : Sample E V → Prop)
    (hbad : ∀ ω ∈ (samplePMF G w s).support, bad ω →
      ∃ u v, LevelResidualPath G (virtualCut X A ω) u v ∧
        a ≤ ∑ e, (levelSeparationValue G (w e) (s e) u v).toReal) :
    ((samplePMF G w s).toMeasure {ω | bad ω}).toReal ≤
      (Fintype.card V : ℝ) ^ 2 * Real.exp (-(A.card : ℝ) * a / (Fintype.card E : ℝ)) := by
  let events : V × V → Set (Sample E V) := fun p =>
    {ω | LevelResidualPath G (virtualCut X A ω) p.1 p.2 ∧
      a ≤ ∑ e, (levelSeparationValue G (w e) (s e) p.1 p.2).toReal}
  have hsub : {ω | bad ω} ∩ (samplePMF G w s).support ⊆ ⋃ p, events p := by
    rintro ω ⟨hbadω, hω⟩
    obtain ⟨u, v, hp, hv⟩ := hbad ω hω hbadω
    exact Set.mem_iUnion.mpr ⟨(u, v), hp, hv⟩
  calc
    _ ≤ ((samplePMF G w s).toMeasure (⋃ p, events p)).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) ((samplePMF G w s).toMeasure_mono
        ((Set.toFinite _).measurableSet) hsub)
    _ ≤ ∑ p, ((samplePMF G w s).toMeasure (events p)).toReal :=
      measureReal_iUnion_fintype_le events
    _ ≤ ∑ _p : V × V, Real.exp (-(A.card : ℝ) * a / (Fintype.card E : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      by_cases hv : a ≤ ∑ e, (levelSeparationValue G (w e) (s e) p.1 p.2).toReal
      · calc
          _ ≤ Real.exp (-(A.card : ℝ) *
              (∑ e, (levelSeparationValue G (w e) (s e) p.1 p.2).toReal) / (Fintype.card E : ℝ)) := by
            simpa [events, hv] using virtual_residualPath_le_exp G w s X A p.1 p.2
          _ ≤ _ := Real.exp_le_exp.mpr (div_le_div_of_nonneg_right
            (mul_le_mul_of_nonpos_left hv (neg_nonpos.mpr (Nat.cast_nonneg _))) (by positivity))
      · simpa [events, hv] using (Real.exp_pos (-(A.card : ℝ) * a / (Fintype.card E : ℝ))).le
    _ = _ := by simp [Fintype.card_prod, pow_two, mul_assoc]

end UnionBound

/-- The actual adaptive overrun event has the frozen exponential tail. -/
theorem active_prefix_probability_le [Nonempty V] (r : ℝ≥0) (hr : 1 < r)
    (S : State G D L) (B : ℝ) (hB : 1 ≤ S.scale) (hcap : (S.scale : ℝ) ≤ B)
    (hL : 64 * B ≤ (L : ℝ)) (hLn : (L : ℝ) ≤ Fintype.card V)
    (hnL : (Fintype.card V : ℝ) ≤ (L : ℝ) ^ 3)
    (t : ℕ) (ht : t ≤ Fintype.card (Label S)) :
    ((samplePMF G (fun p : Label S => S.weight p.val) (fun p => p.val.1)).toMeasure
      {ω | Active r S.mass (epochPrefix r S ω t).state}).toReal ≤
      (Fintype.card V : ℝ) ^ 2 *
        Real.exp (-(t : ℝ) * valueThreshold r S B / (S.remaining.card : ℝ)) := by
  simpa [prefixSet] using valuable_pair_event_le G
    (fun p : Label S => S.weight p.val) (fun p => p.val.1) S.cut (prefixSet S t ht)
    (valueThreshold r S B) (fun ω => Active r S.mass (epochPrefix r S ω t).state)
    (fun ω hω ha => active_prefix_value_witness r hr S B hB hcap hL hLn hnL hω t ht ha)

open FiniteAmplification

/-- The actual finite input distribution at a fixed epoch start. -/
def inputLaw (S : State G D L) : PMF (Sample (Label S) V) :=
  samplePMF G (fun p : Label S => S.weight p.val) (fun p => p.val.1)

/-- The truncated cardinality expectation in real-valued form. -/
theorem expected_prefix_real_le (r : ℝ≥0) (S : State G D L)
    (t : ℕ) (ht : t ≤ Fintype.card (Label S)) :
    expectedCost (inputLaw S) (fun ω => (((epochPrefix r S ω t).state.cut \ S.cut).card : ℝ)) ≤
      (t : ℝ) / (S.remaining.card : ℝ) * S.mass := by
  have h := expected_epochPrefix_new_card_le r S t ht
  have hreal := ENNReal.toReal_mono (by finiteness) h
  change (∑ ω, inputLaw S ω * (((epochPrefix r S ω t).state.cut \ S.cut).card : ℝ≥0∞)).toReal ≤ _ at hreal
  rw [ENNReal.toReal_sum (fun ω _ => ENNReal.mul_ne_top
    ((inputLaw S).apply_ne_top ω) (by finiteness))] at hreal
  simpa only [expectedCost, inputLaw, ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.coe_toReal, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_natCast] using hreal

/-- Full epoch cost equals a truncated cost plus a cost of at most `n` on the
overrun event. This exposes the failure term before any horizon choice. -/
theorem expected_epoch_le_truncation (r : ℝ≥0) (S : State G D L)
    (t : ℕ) (ht : t ≤ Fintype.card (Label S)) :
    expectedCost (inputLaw S) (fun ω => (((epoch r S ω).state.cut \ S.cut).card : ℝ)) ≤
      (t : ℝ) / (S.remaining.card : ℝ) * S.mass +
      (Fintype.card V : ℝ) * probability (inputLaw S)
        (fun ω => Active r S.mass (epochPrefix r S ω t).state) := by
  calc
    _ ≤ expectedCost (inputLaw S)
        (fun ω => (((epochPrefix r S ω t).state.cut \ S.cut).card : ℝ) +
          if Active r S.mass (epochPrefix r S ω t).state then (Fintype.card V : ℝ) else 0) := by
      apply Finset.sum_le_sum
      intro ω hω
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      dsimp only
      exact_mod_cast epoch_new_card_le_prefix_add_failure r S ω t
    _ = expectedCost (inputLaw S)
        (fun ω => (((epochPrefix r S ω t).state.cut \ S.cut).card : ℝ)) +
        (Fintype.card V : ℝ) * probability (inputLaw S)
          (fun ω => Active r S.mass (epochPrefix r S ω t).state) := by
      rw [probability_eq_sum]
      simp only [expectedCost, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro ω hω
      split_ifs <;> ring
    _ ≤ _ := add_le_add (expected_prefix_real_le r S t ht) le_rfl

/-- A positive optimum entails at least one remaining label. -/
theorem remaining_card_pos (S : State G D L) (hpos : S.optimum ≠ 0) :
    0 < S.remaining.card := by
  apply Nat.pos_of_ne_zero
  intro hz
  exact hpos (optimum_eq_zero_of_remaining_empty S (Finset.card_eq_zero.mp hz))

/-- The exact current outside mass is bounded by the actual scale cap. -/
theorem mass_le_card_mul_cap (S : State G D L) :
    S.mass ≤ (S.remaining.card : ℝ≥0) * ((Fintype.card V : ℝ≥0) * S.scale / L) := by
  change (∑ p ∈ S.remaining, CandidateOptimization.outsideMass S.cut (S.weight p)) ≤ _
  calc
    _ ≤ ∑ _p ∈ S.remaining, (Fintype.card V : ℝ≥0) * S.scale / L := by
      apply Finset.sum_le_sum
      intro p hp
      unfold CandidateOptimization.outsideMass
      calc
        _ ≤ ∑ _v ∈ Finset.univ.filter (fun v : V => v ∉ S.cut), S.scale / L := by
          apply Finset.sum_le_sum
          intro v hv
          exact S.cap p hp v (Finset.mem_filter.mp hv).2
        _ = ((Finset.univ.filter (fun v : V => v ∉ S.cut)).card : ℝ≥0) * (S.scale / L) := by simp
        _ ≤ (Fintype.card V : ℝ≥0) * (S.scale / L) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_univ _) zero_le
        _ = _ := by ring
    _ = _ := by simp

/-- Ceiling overhead is controlled by `nB/L` at every epoch start. -/
theorem mass_average_le (S : State G D L) (hpos : S.optimum ≠ 0)
    (B : ℝ) (hcap : (S.scale : ℝ) ≤ B) :
    (S.mass : ℝ) / (S.remaining.card : ℝ) ≤ (Fintype.card V : ℝ) * B / L := by
  have hP : (0 : ℝ) < S.remaining.card := by exact_mod_cast remaining_card_pos S hpos
  have hm : (S.mass : ℝ) ≤ (S.remaining.card : ℝ) * ((Fintype.card V : ℝ) * S.scale / L) := by
    exact_mod_cast mass_le_card_mul_cap S
  apply (div_le_iff₀ hP).mpr
  calc
    _ ≤ _ := hm
    _ ≤ (S.remaining.card : ℝ) * ((Fintype.card V : ℝ) * B / L) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcap (Nat.cast_nonneg _)) (NNReal.coe_nonneg _)
    _ = _ := mul_comm _ _

/-- A horizon chosen from history only, capped by the number of remaining labels. -/
def horizon (r : ℝ≥0) (S : State G D L) (B H : ℝ) : ℕ :=
  min S.remaining.card ⌈(S.remaining.card : ℝ) * H / valueThreshold r S B⌉₊

theorem horizon_le_card (r : ℝ≥0) (S : State G D L) (B H : ℝ) :
    horizon r S B H ≤ S.remaining.card := Nat.min_le_left _ _

/-- The exact ceiling loss in the truncated mass expectation. -/
theorem horizon_cost_le (r : ℝ≥0) (S : State G D L) (B H : ℝ)
    (ha : 0 < valueThreshold r S B) (hH : 0 ≤ H) (hP : 0 < S.remaining.card) :
    (horizon r S B H : ℝ) / (S.remaining.card : ℝ) * S.mass ≤
      H * S.mass / valueThreshold r S B + (S.mass : ℝ) / S.remaining.card := by
  have hPR : (0 : ℝ) < S.remaining.card := by exact_mod_cast hP
  have ht : (horizon r S B H : ℝ) ≤
      (S.remaining.card : ℝ) * H / valueThreshold r S B + 1 := by
    have hceil := (Nat.ceil_lt_add_one (show 0 ≤ (S.remaining.card : ℝ) * H / valueThreshold r S B by positivity)).le
    have htceil : (horizon r S B H : ℝ) ≤ (⌈(S.remaining.card : ℝ) * H / valueThreshold r S B⌉₊ : ℝ) := by
      exact_mod_cast (Nat.min_le_right S.remaining.card ⌈(S.remaining.card : ℝ) * H / valueThreshold r S B⌉₊)
    exact htceil.trans hceil
  calc
    _ ≤ (((S.remaining.card : ℝ) * H / valueThreshold r S B + 1) /
        (S.remaining.card : ℝ)) * S.mass := by gcongr
    _ = _ := by field_simp

/-- At a non-full horizon, the ceiling guarantees the claimed exponential exponent. -/
theorem horizon_exponent (r : ℝ≥0) (S : State G D L) (B H : ℝ)
    (ha : 0 < valueThreshold r S B) (hP : 0 < S.remaining.card)
    (hnotfull : horizon r S B H ≠ S.remaining.card) :
    H ≤ (horizon r S B H : ℝ) * valueThreshold r S B / (S.remaining.card : ℝ) := by
  have hPR : (0 : ℝ) < S.remaining.card := by exact_mod_cast hP
  have heq : horizon r S B H = ⌈(S.remaining.card : ℝ) * H / valueThreshold r S B⌉₊ := by
    unfold horizon at hnotfull ⊢
    exact min_eq_right (le_of_not_ge (fun h => hnotfull (min_eq_left h)))
  rw [heq]
  have hceil := Nat.le_ceil ((S.remaining.card : ℝ) * H / valueThreshold r S B)
  apply (le_div_iff₀ hPR).mpr
  have hc := (div_le_iff₀ ha).mp hceil
  nlinarith

/-- The explicit target scale, reciprocal to the graph-value scale. -/
def sizeFactor (V : Type*) [Fintype V] (L : ℝ≥0) : ℝ :=
  ((Fintype.card V : ℝ) / L) ^ (3 / 2 : ℝ)

theorem valueThreshold_pos [Nonempty V] (r : ℝ≥0) (hr : 1 < r)
    (S : State G D L) (B : ℝ) (hB : 1 ≤ S.scale) (hcap : (S.scale : ℝ) ≤ B)
    (hL : 64 * B ≤ (L : ℝ)) (hpos : S.optimum ≠ 0) : 0 < valueThreshold r S B := by
  have hBR : (1 : ℝ) ≤ S.scale := by exact_mod_cast hB
  have hBp : 0 < B := lt_of_lt_of_le zero_lt_one (hBR.trans hcap)
  have hLp : (0 : ℝ) < L := by linarith
  have hrp : (0 : ℝ) < r := by exact_mod_cast lt_trans zero_lt_one hr
  have hm : (0 : ℝ) < S.mass := by
    have h := (S.one_le_optimum hpos).trans S.optimum_le_mass
    exact_mod_cast lt_of_lt_of_le zero_lt_one h
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  unfold valueThreshold
  exact div_pos (mul_pos hm (Real.rpow_pos_of_pos (div_pos hLp hn) _))
    (mul_pos hrp (graphDenominator_pos _ hBp hrp))

/-- Exact cancellation of the current starting mass in the horizon's leading cost. -/
theorem mass_div_threshold [Nonempty V] (r : ℝ≥0) (hr : 1 < r)
    (S : State G D L) (B : ℝ) (hB : 1 ≤ S.scale) (hcap : (S.scale : ℝ) ≤ B)
    (hL : 64 * B ≤ (L : ℝ)) (hpos : S.optimum ≠ 0) :
    (S.mass : ℝ) / valueThreshold r S B =
      (r : ℝ) * graphDenominator (Fintype.card V) B r * sizeFactor V L := by
  have hBR : (1 : ℝ) ≤ S.scale := by exact_mod_cast hB
  have hLp : (0 : ℝ) < L := by linarith
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hm : (0 : ℝ) < S.mass := by
    exact_mod_cast lt_of_lt_of_le zero_lt_one ((S.one_le_optimum hpos).trans S.optimum_le_mass)
  have hz : 0 < ((L : ℝ) / Fintype.card V) ^ (3 / 2 : ℝ) :=
    Real.rpow_pos_of_pos (div_pos hLp hn) _
  have hinv : (((L : ℝ) / Fintype.card V) ^ (3 / 2 : ℝ))⁻¹ = sizeFactor V L := by
    rw [← Real.inv_rpow (div_nonneg (NNReal.coe_nonneg _) (Nat.cast_nonneg _)), inv_div]
    rfl
  unfold valueThreshold
  calc
    _ = (r : ℝ) * graphDenominator (Fintype.card V) B r /
        (((L : ℝ) / Fintype.card V) ^ (3 / 2 : ℝ)) := by field_simp
    _ = _ := by rw [div_eq_mul_inv, hinv]

omit [DecidableEq V] in
theorem one_le_sizeFactor (hL : (0 : ℝ) < L) (hLn : (L : ℝ) ≤ Fintype.card V) :
    1 ≤ sizeFactor V L :=
  Real.one_le_rpow ((le_div_iff₀ hL).mpr (by simpa using hLn)) (by norm_num)

omit [DecidableEq V] in
theorem ratio_le_sizeFactor (hL : (0 : ℝ) < L) (hLn : (L : ℝ) ≤ Fintype.card V) :
    (Fintype.card V : ℝ) / L ≤ sizeFactor V L := by
  have hratio : (1 : ℝ) ≤ (Fintype.card V : ℝ) / L :=
    (le_div_iff₀ hL).mpr (by simpa using hLn)
  simpa only [sizeFactor, Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hratio
    (by norm_num : (1 : ℝ) ≤ 3 / 2)

/-- Finite outer probability and its discrete measurable realization agree. -/
theorem probability_eq_measure {A : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (p : PMF A) (P : A → Prop) :
    probability p P = (p.toMeasure {a | P a}).toReal := by
  exact congrArg ENNReal.toReal
    (p.toMeasure_apply_eq_toOuterMeasure_apply ((Set.toFinite _).measurableSet)).symm

/-- The capped horizon either processes every label or has exponential failure
at most the pair union bound `n² exp(-H)`. -/
theorem horizon_failure_le [Nonempty V] (r : ℝ≥0) (hr : 1 < r)
    (S : State G D L) (B H : ℝ) (hB : 1 ≤ S.scale) (hcap : (S.scale : ℝ) ≤ B)
    (hL : 64 * B ≤ (L : ℝ)) (hLn : (L : ℝ) ≤ Fintype.card V)
    (hnL : (Fintype.card V : ℝ) ≤ (L : ℝ) ^ 3) (hpos : S.optimum ≠ 0) :
    probability (inputLaw S)
      (fun ω => Active r S.mass (epochPrefix r S ω (horizon r S B H)).state) ≤
      (Fintype.card V : ℝ) ^ 2 * Real.exp (-H) := by
  by_cases hfull : horizon r S B H = S.remaining.card
  · have hno : ∀ ω : Sample (Label S) V,
        ¬Active r S.mass (epochPrefix r S ω (horizon r S B H)).state := by
      intro ω
      simpa only [hfull, Fintype.card_coe] using epochPrefix_full_not_active r S ω
    simp only [probability_eq_sum, ite_eq_right (hno _), Finset.sum_const_zero]
    positivity
  · rw [probability_eq_measure]
    apply le_trans (active_prefix_probability_le r hr S B hB hcap hL hLn hnL
      (horizon r S B H) (by simpa only [Fintype.card_coe] using horizon_le_card r S B H))
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    apply Real.exp_le_exp.mpr
    have he := horizon_exponent r S B H
      (valueThreshold_pos r hr S B hB hcap hL hpos) (remaining_card_pos S hpos) hfull
    convert neg_le_neg he using 1; ring

/-- Explicit full-epoch expectation, including the ceiling and failure costs. -/
theorem expected_epoch_explicit [Nonempty V] (r : ℝ≥0) (hr : 1 < r)
    (S : State G D L) (B H : ℝ) (hB : 1 ≤ S.scale) (hcap : (S.scale : ℝ) ≤ B)
    (hL : 64 * B ≤ (L : ℝ)) (hLn : (L : ℝ) ≤ Fintype.card V)
    (hnL : (Fintype.card V : ℝ) ≤ (L : ℝ) ^ 3) (hpos : S.optimum ≠ 0) (hH : 0 ≤ H) :
    expectedCost (inputLaw S) (fun ω => (((epoch r S ω).state.cut \ S.cut).card : ℝ)) ≤
      (r : ℝ) * graphDenominator (Fintype.card V) B r * H * sizeFactor V L +
        (Fintype.card V : ℝ) * B / L + (Fintype.card V : ℝ) ^ 3 * Real.exp (-H) := by
  apply le_trans (expected_epoch_le_truncation r S (horizon r S B H)
    (by simpa only [Fintype.card_coe] using horizon_le_card r S B H))
  have hcost := horizon_cost_le r S B H (valueThreshold_pos r hr S B hB hcap hL hpos)
    hH (remaining_card_pos S hpos)
  have hfail := mul_le_mul_of_nonneg_left
    (horizon_failure_le r hr S B H hB hcap hL hLn hnL hpos) (Nat.cast_nonneg (Fintype.card V) : (0 : ℝ) ≤ _)
  have havg := mass_average_le S hpos B hcap
  have hcancel := mass_div_threshold r hr S B hB hcap hL hpos
  have he : H * (S.mass : ℝ) / valueThreshold r S B =
      (r : ℝ) * graphDenominator (Fintype.card V) B r * H * sizeFactor V L := by
    rw [mul_div_assoc, hcancel]
    ring
  rw [he] at hcost
  nlinarith

/-- A sufficiently small failure budget is absorbed into the same size scale. -/
def epochCostBound (r : ℝ≥0) (V : Type*) [Fintype V] (L : ℝ≥0) (B H : ℝ) : ℝ :=
  ((r : ℝ) * graphDenominator (Fintype.card V) B r * H + B + 1) * sizeFactor V L

theorem expected_epoch_le [Nonempty V] (r : ℝ≥0) (hr : 1 < r)
    (S : State G D L) (B H : ℝ) (hB : 1 ≤ S.scale) (hcap : (S.scale : ℝ) ≤ B)
    (hL : 64 * B ≤ (L : ℝ)) (hLn : (L : ℝ) ≤ Fintype.card V)
    (hnL : (Fintype.card V : ℝ) ≤ (L : ℝ) ^ 3) (hpos : S.optimum ≠ 0) (hH : 0 ≤ H)
    (hfailure : (Fintype.card V : ℝ) ^ 3 * Real.exp (-H) ≤ 1) :
    expectedCost (inputLaw S) (fun ω => (((epoch r S ω).state.cut \ S.cut).card : ℝ)) ≤
      epochCostBound r V L B H := by
  apply (expected_epoch_explicit r hr S B H hB hcap hL hLn hnL hpos hH).trans
  have hBR : (1 : ℝ) ≤ S.scale := by exact_mod_cast hB
  have hBp : 0 ≤ B := (zero_le_one.trans hBR).trans hcap
  have hLp : (0 : ℝ) < L := by linarith
  have hratio := mul_le_mul_of_nonneg_left (ratio_le_sizeFactor hLp hLn) hBp
  have hone := one_le_sizeFactor hLp hLn
  have hratio' : (Fintype.card V : ℝ) * B / L ≤ B * sizeFactor V L := by
    calc
      _ = B * ((Fintype.card V : ℝ) / L) := by ring
      _ ≤ _ := hratio
  calc
    _ ≤ (r : ℝ) * graphDenominator (Fintype.card V) B r * H * sizeFactor V L +
        B * sizeFactor V L + sizeFactor V L :=
      add_le_add (add_le_add le_rfl hratio') (hfailure.trans hone)
    _ = _ := by unfold epochCostBound; ring

/-- The bounded solver's final cut law, using its genuine finite adaptive binds. -/
def boundedOutput (r : ℝ≥0) (hr : 1 < r) (fuel : ℕ) (S : State G D L) : PMF (Finset V) :=
  (solve r hr fuel S).map State.cut

@[simp] theorem boundedOutput_zero (r : ℝ≥0) (hr : 1 < r) (S : State G D L) :
    boundedOutput r hr 0 S = PMF.pure S.cut := by
  simp [boundedOutput, solve, PMF.pure_map]

theorem boundedOutput_succ (r : ℝ≥0) (hr : 1 < r) (fuel : ℕ) (S : State G D L) :
    boundedOutput r hr (fuel + 1) S =
      if (S.stabilize r hr).optimum = 0 then PMF.pure S.cut else
        (inputLaw (S.stabilize r hr)).bind
          (fun ω => boundedOutput r hr fuel (epoch r (S.stabilize r hr) ω).state) := by
  unfold boundedOutput
  rw [solve]
  split_ifs <;> simp [PMF.pure_map, PMF.map_bind, inputLaw]

/-- Geometric fuel proves validity for every supported final cut. -/
theorem boundedOutput_valid (r : ℝ≥0) (hr : 1 < r) (fuel : ℕ) (S : State G D L)
    (hfuel : S.mass < r ^ fuel) {X : Finset V} (hX : X ∈ (boundedOutput r hr fuel S).support) :
    IsIntegralCut G X (D : Set (V × V)) := by
  obtain ⟨T, hT, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hX
  exact T.integralCut_of_zero (solve_support_zero_of_mass_fuel r hr fuel S
    ((stabilize_mass_le r hr S).trans_lt hfuel) hT)

/-- All actual optimizer installations preserve the initial scale's unit lower bound. -/
theorem execution_scale_one_le (r : ℝ≥0) {S₀ S : State G D L} {k q : ℕ}
    (h : Execution r S₀ k q S) (h₀ : 1 ≤ S₀.scale) : 1 ≤ S.scale := by
  rw [h.scale_eq]
  exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) h₀

/-- The actual control trace supplies the scale invariant used by every epoch. -/
theorem execution_scale_bounds (r : ℝ≥0) (hr : 1 < r) {S₀ S : State G D L} {k q J : ℕ}
    (h : Execution r S₀ k q S) (h₀ : 1 ≤ S₀.scale) (hJ : S₀.mass < r ^ (J + 1))
    (B : ℝ) (hB : ((4 ^ J * S₀.scale : ℝ≥0) : ℝ) ≤ B) :
    1 ≤ S.scale ∧ (S.scale : ℝ) ≤ B := by
  refine ⟨execution_scale_one_le r h h₀, ?_⟩
  apply le_trans _ hB
  exact_mod_cast h.scale_le hr hJ

/-- A finite constant adds its literal value to an expectation. -/
theorem expected_add_const {A : Type*} [Fintype A] (p : PMF A) (f : A → ℝ) (c : ℝ) :
    expectedCost p (fun a => f a + c) = expectedCost p f + c := by
  simp only [expectedCost, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
    sum_probability_toReal, one_mul]

/-- Counting the entire epoch cut decomposes exactly into its start and new vertices. -/
theorem expected_epoch_card (r : ℝ≥0) (S : State G D L) :
    expectedCost (inputLaw S) (fun ω => ((epoch r S ω).state.cut.card : ℝ)) =
      expectedCost (inputLaw S) (fun ω => (((epoch r S ω).state.cut \ S.cut).card : ℝ)) + S.cut.card := by
  have he : ∀ ω : Sample (Label S) V, ((epoch r S ω).state.cut.card : ℝ) =
      (((epoch r S ω).state.cut \ S.cut).card : ℝ) + S.cut.card := by
    intro ω
    exact_mod_cast (Finset.card_sdiff_add_card_eq_card
      (run_cut_subset r S.mass (sampleLevels S ω) S (sampleOrder S ω.1))).symm
  simp_rw [he]
  exact expected_add_const _ _ _

/-- The finite tower identity sums the unconditional epoch bound over bounded
adaptive history. No distribution on the entire optimizer-state type is assumed finite. -/
theorem boundedOutput_expected_of_invariant [Nonempty V] (r : ℝ≥0) (hr : 1 < r)
    (S₀ : State G D L) (B H : ℝ)
    (hinvariant : ∀ (S : State G D L) (k q : ℕ), Execution r S₀ k q S →
      1 ≤ S.scale ∧ (S.scale : ℝ) ≤ B)
    (hL : 64 * B ≤ (L : ℝ)) (hLn : (L : ℝ) ≤ Fintype.card V)
    (hnL : (Fintype.card V : ℝ) ≤ (L : ℝ) ^ 3) (hH : 0 ≤ H)
    (hfailure : (Fintype.card V : ℝ) ^ 3 * Real.exp (-H) ≤ 1)
    (hC : 0 ≤ epochCostBound r V L B H) (fuel : ℕ)
    (S : State G D L) (k q : ℕ) (hS : Execution r S₀ k q S) :
    expectedCost (boundedOutput r hr fuel S) (fun X => (X.card : ℝ)) ≤
      (S.cut.card : ℝ) + (fuel : ℝ) * epochCostBound r V L B H := by
  induction fuel generalizing S k q with
  | zero => simp
  | succ fuel ih =>
      rw [boundedOutput_succ]
      split_ifs with hz
      · simp only [expectedCost_pure]
        exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hC)
      · have hstab : Execution r S₀ (k + S.restartCount r hr) q (S.stabilize r hr) := by
          exact Execution.stabilize_prefix hS hr le_rfl
        have hb := hinvariant _ _ _ hstab
        have hepoch := expected_epoch_le r hr (S.stabilize r hr) B H hb.1 hb.2
          hL hLn hnL hz hH hfailure
        rw [expectedCost_bind]
        calc
          _ ≤ ∑ ω, (inputLaw (S.stabilize r hr) ω).toReal *
              (((epoch r (S.stabilize r hr) ω).state.cut.card : ℝ) +
                (fuel : ℝ) * epochCostBound r V L B H) := by
            apply Finset.sum_le_sum
            intro ω hω
            apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
            exact ih _ _ _ (run_execution r (S.stabilize r hr).mass
              (sampleLevels (S.stabilize r hr) ω) (sampleOrder (S.stabilize r hr) ω.1) hstab)
          _ = expectedCost (inputLaw (S.stabilize r hr))
                (fun ω => (((epoch r (S.stabilize r hr) ω).state.cut \ (S.stabilize r hr).cut).card : ℝ)) +
              S.cut.card + (fuel : ℝ) * epochCostBound r V L B H := by
            change expectedCost (inputLaw (S.stabilize r hr))
              (fun ω => ((epoch r (S.stabilize r hr) ω).state.cut.card : ℝ) +
                (fuel : ℝ) * epochCostBound r V L B H) = _
            rw [expected_add_const, expected_epoch_card, stabilize_cut]
          _ ≤ _ := by
            simp only [Nat.cast_add, Nat.cast_one]
            linarith

/-- The invariant in the tower theorem is derived from the global installation
budget; it is not an optimizer assumption. -/
theorem boundedOutput_expected [Nonempty V] (r : ℝ≥0) (hr : 1 < r)
    (S : State G D L) (J : ℕ) (B H : ℝ) (h₀ : 1 ≤ S.scale)
    (hJ : S.mass < r ^ (J + 1)) (hB : ((4 ^ J * S.scale : ℝ≥0) : ℝ) ≤ B)
    (hL : 64 * B ≤ (L : ℝ)) (hLn : (L : ℝ) ≤ Fintype.card V)
    (hnL : (Fintype.card V : ℝ) ≤ (L : ℝ) ^ 3) (hH : 0 ≤ H)
    (hfailure : (Fintype.card V : ℝ) ^ 3 * Real.exp (-H) ≤ 1) :
    expectedCost (boundedOutput r hr (J + 1) S) (fun X => (X.card : ℝ)) ≤
      (S.cut.card : ℝ) + ((J : ℝ) + 1) * epochCostBound r V L B H := by
  have hbase := execution_scale_bounds r hr (Execution.start (S₀ := S)) h₀ hJ B hB
  have hBp : 0 < B := by
    have hscale : (1 : ℝ) ≤ S.scale := by exact_mod_cast h₀
    linarith [hbase.2]
  have hC : 0 ≤ epochCostBound r V L B H := by
    have hK := (graphDenominator_pos (Fintype.card V) hBp
      (by exact_mod_cast lt_trans zero_lt_one hr)).le
    unfold epochCostBound sizeFactor
    positivity
  simpa only [Nat.cast_add, Nat.cast_one] using boundedOutput_expected_of_invariant r hr S B H
    (fun T k q hT => execution_scale_bounds r hr hT h₀ hJ B hB)
    hL hLn hnL hH hfailure hC (J + 1) S 0 0 Execution.start

end
end DirectedFlowCutGap.AdaptiveCost
