import DirectedFlowCutGap.FlexibleAdaptiveRounding
import DirectedFlowCutGap.GridLevelSampling

/-!
# The integer-grid implementation boundary for flexible adaptive control

A grid optimizer is required only at a natural scale and positive integer
threshold. The hybrid provider has a compact fallback on other states, and
its invariant proves that the fallback is never used from an integral-scale
initial state. Integer mass codes implement the readiness comparison without
comparing real numbers. Producing those codes and implementing the optimizer
are explicit interfaces, not runtime conclusions of this module.
-/
namespace DirectedFlowCutGap.FlexibleGridProvider

/-- This function is genuinely an integer Boolean test. -/
def readyCode (R current optimal : ℕ) : Bool :=
  Nat.beq optimal 0 || Nat.ble current (R * optimal)

noncomputable section
open scoped BigOperators NNReal ENNReal
open CandidateSchedule CandidateSchedule.State CandidateOptimization EpochAccounting
open FlexibleCandidateSchedule
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : Digraph V} {D : Finset (V × V)} {L : ℕ}

/-- The grid theorem has a positive integer denominator. -/
def OnGrid (S : State G D (L : ℝ≥0)) : Prop :=
  ∀ p ∈ S.remaining, ∀ v ∉ S.cut,
    ∃ k : ℤ, 0 ≤ k ∧ (S.weight p v : ℝ) = (k : ℝ) / L

def NaturalScale (S : State G D (L : ℝ≥0)) : Prop :=
  ∃ B : ℕ, S.scale = (B : ℝ≥0)

/-- A grid optimizer returns actual weights, exact optimality, and integer
numerator witnesses. It is only invoked when the scale has a natural code. -/
structure GridMinimum (S : State G D (L : ℝ≥0)) where
  weight : (V × V) → V → ℝ≥0
  feasible : ∀ p ∈ S.remaining,
    IsCandidate G {p} S.cut ((4 * S.scale) / (L : ℝ≥0)) (weight p)
  minimal : ∀ p ∈ S.remaining, ∀ z,
    IsCandidate G {p} S.cut ((4 * S.scale) / (L : ℝ≥0)) z →
    outsideMass S.cut (weight p) ≤ outsideMass S.cut z
  grid : ∀ p ∈ S.remaining, ∀ v ∉ S.cut,
    ∃ k : ℤ, 0 ≤ k ∧ (weight p v : ℝ) = (k : ℝ) / L

/-- Only grid-cap optimization is an implementation obligation. The state
weights are used to certify nonemptiness, not as an arbitrary-real LP input. -/
abbrev GridOptimizer (G : Digraph V) (D : Finset (V × V)) (L : ℕ) :=
  ∀ (S : State G D (L : ℝ≥0)) (B : ℕ), S.scale = (B : ℝ≥0) → GridMinimum S

/-- The finite-grid existence theorem supplies a mathematical implementation
of the interface. This is not the bounded closure/max-flow implementation. -/
def finiteGridOptimizer (hL : 0 < L) : GridOptimizer G D L := by
  intro S B hB
  have hex (p : V × V) : ∃ w : V → ℝ≥0, p ∈ S.remaining →
      IsCandidate G {p} S.cut ((4 * S.scale) / (L : ℝ≥0)) w ∧
      (∀ v ∉ S.cut, ∃ k : ℤ, 0 ≤ k ∧ (w v : ℝ) = (k : ℝ) / L) ∧
      ∀ z, IsCandidate G {p} S.cut ((4 * S.scale) / (L : ℝ≥0)) z →
        outsideMass S.cut w ≤ outsideMass S.cut z := by
    by_cases hp : p ∈ S.remaining
    · have hcap : ((4 * B : ℕ) : ℝ≥0) = 4 * S.scale := by simp [hB]
      obtain ⟨w, hw⟩ := CandidateGridOptimizer.exists_candidate_grid_minimum
        G p.1 p.2 S.cut L (4 * B) hL (S.candidate p)
          (by simpa only [hcap] using (S.candidate_spec hp).1)
      exact ⟨w, fun _ => by simpa only [hcap] using hw⟩
    · exact ⟨S.weight p, fun h => (hp h).elim⟩
  choose w hw using hex
  exact ⟨w, fun p hp => (hw p hp).1, fun p hp => (hw p hp).2.2,
    fun p hp => (hw p hp).2.1⟩

/-- A grid optimizer is extended mathematically outside its implementation
invariant. The fallback is ruled out along every relevant trace below. -/
def selected (Q : GridOptimizer G D L) (S : State G D (L : ℝ≥0)) :
    (V × V) → V → ℝ≥0 :=
  if h : NaturalScale S then
    (Q S (Classical.choose h) (Classical.choose_spec h)).weight
  else S.candidate

def provider (Q : GridOptimizer G D L) : FamilyProvider G D (L : ℝ≥0) where
  family := selected Q
  feasible := by
    intro S p hp
    unfold selected
    split_ifs with h
    · exact (Q S (Classical.choose h) (Classical.choose_spec h)).feasible p hp
    · exact (S.candidate_spec hp).1
  minimal := by
    intro S p hp z hz
    unfold selected
    split_ifs with h
    · exact (Q S (Classical.choose h) (Classical.choose_spec h)).minimal p hp z hz
    · exact (S.candidate_spec hp).2.2 z hz

theorem selected_eq_grid (Q : GridOptimizer G D L) (S : State G D (L : ℝ≥0))
    (h : NaturalScale S) :
    (provider Q).family S = (Q S (Classical.choose h) (Classical.choose_spec h)).weight := by
  simp only [provider, selected, dite_eq_left h]

/-- The hybrid branch agrees with the optimizer at the explicitly supplied
integer scale, not just an existentially chosen scale code. -/
theorem selected_eq_of_scale (Q : GridOptimizer G D L) (S : State G D (L : ℝ≥0))
    (B : ℕ) (hB : S.scale = (B : ℝ≥0)) :
    (provider Q).family S = (Q S B hB).weight := by
  let hs : NaturalScale S := ⟨B, hB⟩
  have he : Classical.choose hs = B := by
    exact_mod_cast (Classical.choose_spec hs).symm.trans hB
  rw [selected_eq_grid Q S hs]
  have he' : (⟨Classical.choose hs, Classical.choose_spec hs⟩ :
      {b : ℕ // S.scale = (b : ℝ≥0)}) = ⟨B, hB⟩ := Subtype.ext he
  exact congrArg (fun b : {b : ℕ // S.scale = (b : ℝ≥0)} => (Q S b.val b.property).weight) he' 

theorem install_onGrid (Q : GridOptimizer G D L) (S : State G D (L : ℝ≥0))
    (h : NaturalScale S) : OnGrid (S.selectedInstall (provider Q)) := by
  intro p hp v hv
  change ∃ k : ℤ, 0 ≤ k ∧ (((provider Q).family S p v) : ℝ) = (k : ℝ) / L
  rw [selected_eq_grid Q S h]
  exact (Q S (Classical.choose h) (Classical.choose_spec h)).grid p hp v hv

theorem install_naturalScale (Q : GridOptimizer G D L) (S : State G D (L : ℝ≥0))
    (h : NaturalScale S) : NaturalScale (S.selectedInstall (provider Q)) := by
  obtain ⟨B, hB⟩ := h
  exact ⟨4 * B, by simp [State.selectedInstall, hB]⟩

theorem round_onGrid (S : State G D (L : ℝ≥0)) (h : OnGrid S)
    (p : V × V) (hp : p ∈ S.remaining) (d : ℝ≥0) (hd : d ≤ 1) :
    OnGrid (S.round p hp d hd) := by
  intro q hq v hv
  exact h q (Finset.mem_of_mem_erase hq) v
    (fun hvS => hv (Finset.mem_union_left _ hvS))

/-- Integer scale is preserved on every trace, independently of the weight
encoding. Thus every reached restart uses the grid branch of the provider. -/
theorem trace_naturalScale (Q : GridOptimizer G D L) {r : ℝ≥0}
    {S₀ S : State G D (L : ℝ≥0)} {k q : ℕ}
    (h : Trace (provider Q) r S₀ k q S) (hs : NaturalScale S₀) : NaturalScale S := by
  obtain ⟨B, hB⟩ := hs
  refine ⟨4 ^ k * B, ?_⟩
  rw [h.scale_eq, hB]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

theorem trace_invariant (Q : GridOptimizer G D L) {r : ℝ≥0}
    {S₀ S : State G D (L : ℝ≥0)} {k q : ℕ}
    (h : Trace (provider Q) r S₀ k q S) (hs : NaturalScale S₀) (hg : OnGrid S₀) :
    NaturalScale S ∧ OnGrid S := by
  induction h with
  | start => exact ⟨hs, hg⟩
  | restart h hbad ih => exact ⟨install_naturalScale Q _ ih.1, install_onGrid Q _ ih.1⟩
  | sample h hready hpos p hp d hd ih => exact ⟨ih.1, round_onGrid _ ih.2 p hp d hd⟩

/-- The entire new outer law stays in the optimizer's grid domain. -/
theorem solve_support_invariant (Q : GridOptimizer G D L) (r : ℝ≥0) (hr : 1 < r)
    (fuel : ℕ) (S : State G D (L : ℝ≥0)) (hs : NaturalScale S) (hg : OnGrid S)
    {T : State G D (L : ℝ≥0)}
    (hT : T ∈ (FlexibleAdaptiveRounding.solve (provider Q) r hr fuel S).support) :
    NaturalScale T ∧ OnGrid T := by
  obtain ⟨k, q, h⟩ := FlexibleAdaptiveRounding.solve_support_execution (provider Q) r hr fuel S hT
  exact trace_invariant Q h hs hg

/-- Natural numerators make both stop tests finite integer comparisons. -/
structure MassCode (S : State G D (L : ℝ≥0)) where
  current : ℕ
  optimal : ℕ
  current_eq : S.mass = (current : ℝ≥0) / L
  optimal_eq : S.optimum = (optimal : ℝ≥0) / L

theorem readyCode_correct (hL : 0 < L) (R : ℕ)
    (S : State G D (L : ℝ≥0)) (C : MassCode S) :
    readyCode R C.current C.optimal = true ↔ S.Ready (R : ℝ≥0) := by
  have hLp : (0 : ℝ≥0) < L := by exact_mod_cast hL
  have hz : (C.optimal : ℝ≥0) / (L : ℝ≥0) = 0 ↔ C.optimal = 0 := by
    simp [div_eq_zero_iff, ne_of_gt hLp]
  have hm : (C.current : ℝ≥0) / (L : ℝ≥0) ≤
      (R : ℝ≥0) * ((C.optimal : ℝ≥0) / (L : ℝ≥0)) ↔ C.current ≤ R * C.optimal := by
    rw [← mul_div_assoc, div_le_div_iff_of_pos_right hLp]
    exact_mod_cast Iff.rfl
  simp only [readyCode, Bool.or_eq_true, Nat.beq_eq, Nat.ble_eq, State.Ready,
    C.current_eq, C.optimal_eq, hz, hm]

/-- The outer solver's zero-optimum stop is also an integer comparison. -/
theorem zeroCode_correct (hL : 0 < L) (S : State G D (L : ℝ≥0)) (C : MassCode S) :
    Nat.beq C.optimal 0 = true ↔ S.optimum = 0 := by
  have hLp : (0 : ℝ≥0) < L := by exact_mod_cast hL
  simp only [Nat.beq_eq, C.optimal_eq, div_eq_zero_iff, Nat.cast_eq_zero,
    ne_of_gt hLp, or_false]

/-- The data bridge for the finite gate. The mathematical instance below sums
the grid weights; an executable implementation may directly retain their codes. -/
abbrev CodeProvider (G : Digraph V) (D : Finset (V × V)) (L : ℕ) :=
  ∀ S : State G D (L : ℝ≥0), NaturalScale S → OnGrid S → MassCode S

/-- Every grid family has an exact natural numerator for its outside mass. -/
theorem exists_mass_numerator (S : State G D (L : ℝ≥0)) (hg : OnGrid S) :
    ∃ n : ℕ, S.mass = (n : ℝ≥0) / L := by
  have hex : ∀ (p : V × V) (v : V), ∃ k : ℕ,
      p ∈ S.remaining → v ∉ S.cut → (S.weight p v : ℝ) = (k : ℝ) / L := by
    intro p v
    by_cases hp : p ∈ S.remaining
    · by_cases hv : v ∉ S.cut
      · obtain ⟨k, hk, he⟩ := hg p hp v hv
        refine ⟨k.toNat, fun _ _ => ?_⟩
        rw [he]
        congr 1
        exact_mod_cast (Int.toNat_of_nonneg hk).symm
      · exact ⟨0, fun _ h => (hv h).elim⟩
    · exact ⟨0, fun h _ => (hp h).elim⟩
  choose k hk using hex
  refine ⟨∑ p ∈ S.remaining, ∑ v ∈ Finset.univ.filter (fun v => v ∉ S.cut), k p v, ?_⟩
  apply NNReal.coe_injective
  simp only [State.mass, familyMass, outsideMass, NNReal.coe_sum, NNReal.coe_div,
    NNReal.coe_natCast, Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro v hv
  exact hk p v hp (Finset.mem_filter.mp hv).2

/-- Codes exist by summing the actual current and selected integer families.
This classical extraction establishes correctness, not executable encoding cost. -/
def codeProvider (Q : GridOptimizer G D L) : CodeProvider G D L := by
  intro S hs hg
  let ha := exists_mass_numerator S hg
  let hb := exists_mass_numerator (S.selectedInstall (provider Q)) (install_onGrid Q S hs)
  exact ⟨Classical.choose ha, Classical.choose hb, Classical.choose_spec ha,
    by simpa only [selectedInstall_mass] using Classical.choose_spec hb⟩

/-- The invariant used by the grid-only implementation. -/
abbrev GridState (G : Digraph V) (D : Finset (V × V)) (L : ℕ) :=
  {S : State G D (L : ℝ≥0) // NaturalScale S ∧ OnGrid S}

/-- Bounded integer-test control: the only branch compares natural numerators.
The supplied optimizer and code functions are separately visible data. -/
def codedAdvance (Q : GridOptimizer G D L) (C : CodeProvider G D L) (R : ℕ)
    (S : GridState G D L) : GridState G D L :=
  if readyCode R (C S.val S.property.1 S.property.2).current
      (C S.val S.property.1 S.property.2).optimal then S
  else ⟨S.val.selectedInstall (provider Q), install_naturalScale Q _ S.property.1,
    install_onGrid Q _ S.property.1⟩

theorem codedAdvance_val (Q : GridOptimizer G D L) (C : CodeProvider G D L)
    (hL : 0 < L) (R : ℕ) (S : GridState G D L) :
    (codedAdvance Q C R S).val = S.val.selectedAdvance (provider Q) (R : ℝ≥0) := by
  have he := readyCode_correct hL R S.val (C S.val S.property.1 S.property.2)
  unfold codedAdvance State.selectedAdvance
  split_ifs with h₁ h₂ h₂
  · rfl
  · exact (h₂ (he.mp h₁)).elim
  · exact (h₁ (he.mpr h₂)).elim
  · rfl

def codedTrajectory (Q : GridOptimizer G D L) (C : CodeProvider G D L) (R : ℕ)
    (S : GridState G D L) : ℕ → GridState G D L
  | 0 => S
  | n + 1 => codedAdvance Q C R (codedTrajectory Q C R S n)

theorem codedTrajectory_val (Q : GridOptimizer G D L) (C : CodeProvider G D L)
    (hL : 0 < L) (R : ℕ) (S : GridState G D L) (N : ℕ) :
    (codedTrajectory Q C R S N).val = S.val.selectedTrajectory (provider Q) (R : ℝ≥0) N := by
  induction N with
  | zero => rfl
  | succ N ih =>
      rw [codedTrajectory, codedAdvance_val Q C hL, ih, selectedTrajectory_succ]

/-- Integer-test execution realizes the analyzed stabilizer with an explicit
finite budget, preserving the chosen optimizer's actual state vector. -/
theorem codedTrajectory_eq_stabilize (Q : GridOptimizer G D L) (C : CodeProvider G D L)
    (hL : 0 < L) (R : ℕ) (hR : 1 < (R : ℝ≥0)) (S : GridState G D L)
    (N : ℕ) (hN : S.val.mass < (R : ℝ≥0) ^ N) :
    (codedTrajectory Q C R S N).val = S.val.selectedStabilize (provider Q) (R : ℝ≥0) hR := by
  rw [codedTrajectory_val Q C hL]
  exact S.val.selectedTrajectory_eq_stabilize (provider Q) (R : ℝ≥0) hR N hN

/-- The uniform initial state lies on the integer denominator grid. -/
theorem initial_onGrid (hL : 1 ≤ (L : ℝ≥0)) : OnGrid (initial G (L : ℝ≥0) hL) := by
  intro p hp v hv
  exact ⟨1, by norm_num, by simp [initial]⟩

theorem initial_naturalScale (hL : 1 ≤ (L : ℝ≥0)) :
    NaturalScale (initial G (L : ℝ≥0) hL) := ⟨1, by simp [initial]⟩

/-- Sampling needs grid weights at every vertex, including vertices already
in the cut. This stronger invariant is preserved because rounds freeze weights. -/
def AllWeightsOnGrid (S : State G D (L : ℝ≥0)) : Prop :=
  ∀ p ∈ S.remaining, GridLevelSampling.OnGrid L (S.weight p)

theorem install_allWeightsOnGrid (Q : GridOptimizer G D L) (hL : 0 < L)
    (S : State G D (L : ℝ≥0)) (hs : NaturalScale S) :
    AllWeightsOnGrid (S.selectedInstall (provider Q)) := by
  intro p hp
  apply GridLevelSampling.onGrid_of_unit_inside hL S.cut
  · exact ((provider Q).feasible S p hp).2.1
  · exact install_onGrid Q S hs p hp

theorem round_allWeightsOnGrid (S : State G D (L : ℝ≥0)) (hg : AllWeightsOnGrid S)
    (p : V × V) (hp : p ∈ S.remaining) (d : ℝ≥0) (hd : d ≤ 1) :
    AllWeightsOnGrid (S.round p hp d hd) := by
  intro q hq
  exact hg q (Finset.mem_of_mem_erase hq)

theorem trace_allWeightsOnGrid (Q : GridOptimizer G D L) (hL : 0 < L) {r : ℝ≥0}
    {S₀ S : State G D (L : ℝ≥0)} {k q : ℕ}
    (h : Trace (provider Q) r S₀ k q S) (hs : NaturalScale S₀) (hg : AllWeightsOnGrid S₀) :
    NaturalScale S ∧ AllWeightsOnGrid S := by
  induction h with
  | start => exact ⟨hs, hg⟩
  | restart h hbad ih =>
      exact ⟨install_naturalScale Q _ ih.1, install_allWeightsOnGrid Q hL _ ih.1⟩
  | sample h hready hpos p hp d hd ih =>
      exact ⟨ih.1, round_allWeightsOnGrid _ ih.2 p hp d hd⟩

theorem initial_allWeightsOnGrid (hL : 1 ≤ (L : ℝ≥0)) :
    AllWeightsOnGrid (initial G (L : ℝ≥0) hL) := by
  intro p hp v
  exact ⟨1, by simp [initial]⟩

/-- Every remaining label on a reached state has exactly the finite midpoint
cut law. This identifies the actual joint cut outcome, not representative levels. -/
theorem trace_gridCutPMF_eq (Q : GridOptimizer G D L) (hL : 0 < L) {r : ℝ≥0}
    {S₀ S : State G D (L : ℝ≥0)} {k q : ℕ}
    (h : Trace (provider Q) r S₀ k q S) (hs : NaturalScale S₀) (hg : AllWeightsOnGrid S₀)
    (p : V × V) (hp : p ∈ S.remaining) :
    GridLevelSampling.gridCutPMF G (S.weight p) p.1 L hL =
      FiniteCutLaw.cutPMF G (S.weight p) p.1 := by
  exact GridLevelSampling.gridCutPMF_eq_cutPMF G (S.weight p) p.1 L hL
    ((trace_allWeightsOnGrid Q hL h hs hg).2 p hp)

end
end DirectedFlowCutGap.FlexibleGridProvider
