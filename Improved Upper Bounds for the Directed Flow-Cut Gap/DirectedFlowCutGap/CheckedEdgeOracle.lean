import DirectedFlowCutGap.AdaptiveOracleFailure

/-!
# A checked call to the encoded edge solver

An actual sampled cut is accepted after an exact rational price comparison.
The distribution of rejection on fractionally feasible inputs is bounded
by the established amplified failure estimate. This is a single oracle
call, so the bound can be applied to the current adaptive costs.
-/

namespace DirectedFlowCutGap.CheckedEdgeOracle

open scoped NNReal NNRat ENNReal BigOperators
open FiniteDrawTrees EncodedEdgeLineInput EncodedEdgeSolver

abbrev Edges (n : ℕ) := Finset (Fin n × Fin n)

def costQ {n : ℕ} (D : Input n) (X : Edges n) : ℚ≥0 :=
  ∑ e ∈ X.filter (fun e => D.adjacency[e.1.val][e.2.val] = true), D.costs[e.1.val][e.2.val].value

theorem costQ_value {n : ℕ} (D : Input n) (X : Edges n) :
    (costQ D X : ℝ) = (edgeCutCost D.graph D.cost X : ℝ) := by
  classical
  simp only [costQ, edgeCutCost, NNRat.cast_sum, NNReal.coe_sum, Input.cost, RawNonnegativeRational.Code.realValue]
  apply Finset.sum_congr
  · exact Finset.filter_congr (fun _ _ => Iff.rfl)
  · intro _ _
    rfl

def check {n : ℕ} (D : Input n) (B : ℚ≥0) : Output n → Option (Edges n)
  | .cut mask =>
    let X := EncodedEdgeRounding.selectedEdges mask
    if costQ D X ≤ 2 * B then some X else none
  | .infeasible _ | .invalid => none

inductive Strategy
  | mass
  | size
  deriving DecidableEq

def Strategy.model : Strategy → Mode
  | .mass => massMode
  | .size => sizeMode

private theorem mode_valid {n : ℕ} (choice : Strategy) (κ : ℕ) (D : Input n) {out : Output n}
    (h : out ∈ (ideal (bitTree κ D choice.model)).support) : Valid D out := by
  cases choice
  · exact mass_support_valid κ D h
  · exact size_support_valid κ D h

private theorem mode_within (choice : Strategy) (m : ℕ) (I : EncodedUnitCostReplication.Input m) :
    Within (EncodedUniformRounding.drawBound (4*m^2)) (choice.model m I) := by
  cases choice
  · exact EncodedWeightedRounding.tree_within I
  · exact EncodedSizeRounding.tree_within I

def tree {n : ℕ} (choice : Strategy) (κ : ℕ) (D : Input n) (B : ℚ≥0) :
    FiniteDrawTrees.Tree (Option (Edges n)) :=
  map (check D B) (bitTree κ D choice.model)

theorem tree_within {n : ℕ} (choice : Strategy) (κ : ℕ) (D : Input n) (B : ℚ≥0) :
    Within (EncodedSolverBits.edgeBudget κ D) (tree choice κ D B) := by
  cases choice
  · exact within_map (EncodedSolverBits.edge_mass_within κ D) _
  · exact within_map (EncodedSolverBits.edge_size_within κ D) _

theorem tree_binary {n : ℕ} (choice : Strategy) (κ : ℕ) (D : Input n) (B : ℚ≥0) :
    LazyFairBitTrees.Binary (tree choice κ D B) :=
  LazyFairBitTrees.binary_map (bitTree_binary κ D choice.model) _

theorem accepted {n : ℕ} (choice : Strategy) (κ : ℕ) (D : Input n) (B : ℚ≥0) (X : Edges n)
    (h : some X ∈ (ideal (tree choice κ D B)).support) :
    X ⊆ graphEdges D.graph ∧ IsIntegralEdgeCut D.graph X {d | d ∈ D.demands} ∧ costQ D X ≤ 2 * B := by
  simp only [tree, ideal, law_map] at h
  obtain ⟨out, hout, he⟩ := (PMF.mem_support_map_iff _ _ _).mp h
  cases out with
  | infeasible _ | invalid => cases he
  | cut mask =>
    unfold check at he
    dsimp only at he
    split at he
    · rename_i hcost
      cases he
      have hv := mode_valid choice κ D hout
      exact ⟨hv.1, hv.2, hcost⟩
    · cases he

private theorem failure_check {n : ℕ} (D : Input n) (B : ℚ≥0)
    (feasible : ∃ w, IsFractionalEdgeCut D.graph w {d | d ∈ D.demands})
    {out : Output n} (hv : Valid D out) :
    check D B out = none ↔ 2 * (B : ℝ) < outputPrice D out := by
  cases out with
  | invalid => exact False.elim hv
  | infeasible _ => exact False.elim (hv feasible)
  | cut mask =>
    simp only [check, outputPrice, outputEdges]
    rw [← costQ_value D]
    have h : (2 * (B : ℝ) < (costQ D (EncodedEdgeRounding.selectedEdges mask) : ℝ)) ↔
        2 * B < costQ D (EncodedEdgeRounding.selectedEdges mask) := by
      norm_cast
    rw [h]
    split
    · rename_i hc
      simp [not_lt_of_ge hc]
    · rename_i hc
      simp [lt_of_not_ge hc]

theorem failure {n : ℕ} (choice : Strategy) (κ : ℕ) (D : Input n) (B : ℚ≥0)
    (he : expectedPrice D choice.model ≤ (B : ℝ))
    (feasible : ∃ w, IsFractionalEdgeCut D.graph w {d | d ∈ D.demands}) :
    ideal (tree choice κ D B) none ≤ ENNReal.ofReal (((max 1 n : ℕ) : ℝ) ^ (-(κ : ℝ))) := by
  let p := ideal (bitTree κ D choice.model)
  have hLaw : ideal (tree choice κ D B) = p.map (check D B) := law_map _ _ _
  have hf : ideal (tree choice κ D B) none =
      p.toOuterMeasure {out | 2 * (B : ℝ) < outputPrice D out} := by
    rw [hLaw, ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
    apply p.toOuterMeasure_apply_eq_of_inter_support_eq
    ext a
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h, hp⟩
      exact ⟨(failure_check D B feasible (mode_valid choice κ D hp)).mp h, hp⟩
    · rintro ⟨h, hp⟩
      exact ⟨(failure_check D B feasible (mode_valid choice κ D hp)).mpr h, hp⟩
  rcases eq_or_lt_of_le (show 0 ≤ B from zero_le) with hB | hB
  · subst B
    have hzero : p.toOuterMeasure {out | 2 * ((0 : ℚ≥0) : ℝ) < outputPrice D out} = 0 := by
      rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
      intro a hp ha
      have h := zero_price_on_support κ D choice.model (by simpa using he) hp
      simp [h] at ha
    rw [hf, hzero]
    exact zero_le
  · have htail := polynomial_failure_le κ D choice.model (mode_within choice)
      (B : ℝ) (NNRat.cast_pos.mpr hB) he
    change (p.toOuterMeasure {out | 2 * (B : ℝ) < outputPrice D out}).toReal ≤ _ at htail
    have hcast := ENNReal.ofReal_le_ofReal htail
    rw [← hf, ENNReal.ofReal_toReal ((ideal (tree choice κ D B)).apply_ne_top none)] at hcast
    exact hcast

abbrev mass {n : ℕ} (κ : ℕ) (D : Input n) (B : ℚ≥0) := tree .mass κ D B

theorem mass_within {n : ℕ} (κ : ℕ) (D : Input n) (B : ℚ≥0) :
    Within (EncodedSolverBits.edgeBudget κ D) (mass κ D B) := tree_within .mass κ D B

theorem mass_binary {n : ℕ} (κ : ℕ) (D : Input n) (B : ℚ≥0) :
    LazyFairBitTrees.Binary (mass κ D B) := tree_binary .mass κ D B

theorem mass_accepted {n : ℕ} (κ : ℕ) (D : Input n) (B : ℚ≥0) (X : Edges n)
    (h : some X ∈ (ideal (mass κ D B)).support) :
    X ⊆ graphEdges D.graph ∧ IsIntegralEdgeCut D.graph X {d | d ∈ D.demands} ∧ costQ D X ≤ 2 * B :=
  accepted .mass κ D B X h

theorem mass_failure {n : ℕ} (κ : ℕ) (D : Input n) (B : ℚ≥0)
    (he : expectedPrice D massMode ≤ (B : ℝ))
    (feasible : ∃ w, IsFractionalEdgeCut D.graph w {d | d ∈ D.demands}) :
    ideal (mass κ D B) none ≤ ENNReal.ofReal (((max 1 n : ℕ) : ℝ) ^ (-(κ : ℝ))) :=
  failure .mass κ D B he feasible

end DirectedFlowCutGap.CheckedEdgeOracle
