import DirectedFlowCutGap.WeakDecomposition

/-!
# Weak edge decompositions from an exact-weight oracle

The original edge costs and weights serve as the oracle instance. The
bounded-sampling construction uses the ambient ordered-pair cardinality
for its horizon. It gives the stated loss for the original weight vector,
with a quadratic cardinality factor in the family size.
-/

namespace DirectedFlowCutGap.WeakDecomposition

noncomputable section
open scoped NNReal
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

def exactEdgeHorizon (G : Digraph V) (w : V × V → ℝ≥0) (α : ℝ) : ℕ :=
  BoundedSampling.horizon (fun e => (actualEdgeWeight G w e : ℝ)) α

omit [DecidableEq V] in
theorem exactEdgeHorizon_eq (G : Digraph V) (w : V × V → ℝ≥0) (α : ℝ) :
    exactEdgeHorizon G w α =
      ⌈2 * (Fintype.card V : ℝ)^2 *
        Real.log (4 * α * (Fintype.card V : ℝ)^2 * (totalEdgeWeight G w : ℝ) +
          (Fintype.card V : ℝ)^2)⌉₊ + 1 := by
  classical
  simp only [exactEdgeHorizon, BoundedSampling.horizon, sum_actualEdgeWeight,
    Fintype.card_prod, Nat.cast_mul, pow_two]

omit [DecidableEq V] in
theorem exactEdgeHorizon_pos (G : Digraph V) (w : V × V → ℝ≥0) (α : ℝ) :
    0 < exactEdgeHorizon G w α := Nat.zero_lt_succ _

theorem edge_family_of_exact_weight_factor
    (G : Digraph V) (w : V × V → ℝ≥0) (α : ℝ)
    (h : HasEdgeRoundingFactor G w α) :
    ∃ X : Fin (exactEdgeHorizon G w α) → Finset (V × V),
      (∀ i, X i ⊆ graphEdges G ∧ IsIntegralEdgeCut G (X i) (edgeThresholdDemands G w)) ∧
      ∀ e, ((Finset.univ.filter fun i => e ∈ X i).card : ℝ) /
        (exactEdgeHorizon G w α : ℝ) ≤ 8 * α * (w e : ℝ) := by
  by_cases hn : 0 < Fintype.card (V × V)
  · by_cases hα : 0 < α
    · have hh := BoundedSampling.exists_bounded_family
        (fun e => (actualEdgeWeight G w e : ℝ)) α
        (fun X => X ⊆ graphEdges G ∧ IsIntegralEdgeCut G X (edgeThresholdDemands G w))
        hn (fun e => (actualEdgeWeight G w e).coe_nonneg) hα h.real_cost_round
      obtain ⟨X, hX, _, hbound⟩ := hh
      refine ⟨X, hX, fun e => (hbound e).trans ?_⟩
      apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 8 * α)
      have hle : actualEdgeWeight G w e ≤ w e := by
        unfold actualEdgeWeight
        split_ifs <;> simp
      exact NNReal.coe_le_coe.mpr hle
    · have hzero : α = 0 := le_antisymm (le_of_not_gt hα) h.nonneg
      let c : V × V → ℝ := fun _ => 1
      obtain ⟨X, hX, hcost⟩ := h.real_cost_round c (fun _ => zero_le_one)
      have hc : (X.card : ℝ) ≤ 0 := by
        simpa [c, hzero] using hcost
      have he : X = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp (by exact_mod_cast hc))
      subst X
      exact ⟨fun _ => ∅, fun _ => hX, by simp [hzero]⟩
  · have hzero : Fintype.card (V × V) = 0 := by omega
    let : IsEmpty (V × V) := Fintype.card_eq_zero_iff.mp hzero
    refine ⟨fun _ => ∅, fun _ => ⟨Finset.empty_subset _, ?_⟩, ?_⟩
    · intro s t
      exact isEmptyElim (s, t)
    · intro e
      exact isEmptyElim e

theorem edge_law_of_exact_weight_factor
    (G : Digraph V) (w : V × V → ℝ≥0) (α : ℝ)
    (h : HasEdgeRoundingFactor G w α) :
    ∃ p : PMF (Finset (V × V)),
      (∀ X ∈ p.support, X ⊆ graphEdges G ∧ IsIntegralEdgeCut G X (edgeThresholdDemands G w)) ∧
      ∀ e, (p.toOuterMeasure {X | e ∈ X}).toReal ≤ 8 * α * (w e : ℝ) := by
  obtain ⟨X, hX, hbound⟩ := edge_family_of_exact_weight_factor G w α h
  have ht := exactEdgeHorizon_pos G w α
  refine ⟨familyLaw ht X, ?_, ?_⟩
  · intro Y hY
    exact familyLaw_support ht X
      (fun Z => Z ⊆ graphEdges G ∧ IsIntegralEdgeCut G Z (edgeThresholdDemands G w)) hX hY
  · intro e
    rw [familyLaw_marginal]
    exact hbound e

end
end DirectedFlowCutGap.WeakDecomposition
