import DirectedFlowCutGap.WeakDecompositionSmallMass

/-! Zero-weight arcs do not contribute to the penalty budget of the
original-factor uniform edge construction. -/
namespace DirectedFlowCutGap.WeakDecomposition

noncomputable section
open scoped NNReal BigOperators
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

def positiveArcs (G : Digraph V) (w : V × V → ℝ≥0) : Finset (V × V) :=
  (graphEdges G).filter fun e => 0 < w e

theorem smallEdgeMass_le_positive_arc_count (G : Digraph V) (w : V × V → ℝ≥0) (cutoff : ℝ)
    (nonneg : 0 ≤ cutoff) : smallEdgeMass G w cutoff ≤ ((positiveArcs G w).card : ℝ)*cutoff := by
  let light := Finset.univ.filter fun e => (actualEdgeWeight G w e : ℝ) ≤ cutoff
  let positive := positiveArcs G w
  have filtered : (∑ e ∈ light ∩ positive, (actualEdgeWeight G w e : ℝ)) =
      ∑ e ∈ light, (actualEdgeWeight G w e : ℝ) := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro e lightMem excluded
    have absent : e ∉ positive := fun active => excluded (Finset.mem_inter.mpr ⟨lightMem,active⟩)
    by_cases arc : G.Adj e.1 e.2
    · have weightZero : w e = 0 := le_antisymm (le_of_not_gt fun pos =>
        absent (Finset.mem_filter.mpr ⟨(mem_graphEdges G e).mpr arc,pos⟩)) bot_le
      rw [actualEdgeWeight_of_adj G w arc,weightZero,NNReal.coe_zero]
    · rw [actualEdgeWeight_of_not_adj G w arc,NNReal.coe_zero]
  change (∑ e ∈ light, (actualEdgeWeight G w e : ℝ)) ≤ (positive.card : ℝ)*cutoff
  rw [← filtered]
  calc
    _ ≤ ∑ _e ∈ light ∩ positive, cutoff := Finset.sum_le_sum (fun e h =>
      (Finset.mem_filter.mp (Finset.mem_inter.mp h).1).2)
    _ = ((light ∩ positive).card : ℝ)*cutoff := by simp [nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr
      (Finset.card_le_card Finset.inter_subset_right)) nonneg

end
end DirectedFlowCutGap.WeakDecomposition

namespace DirectedFlowCutGap.ExactFlowCutGap
noncomputable section
open scoped NNReal BigOperators
open WeakDecomposition

theorem edge_uniform_at_original_positive_arc_count {n : ℕ} (hn : 0 < n)
    (G : Digraph (Fin n)) (w : Fin n × Fin n → ℝ≥0) :
    let α : ℝ := efg n (totalEdgeWeight G w)
    let k := max 1 (positiveArcs G w).card
    let T := smallMassHorizon n k (totalEdgeWeight G w) α
    ∃ X : Fin T → Finset (Fin n × Fin n),
      let p := familyLaw (show 0 < T from Nat.zero_lt_succ _) X
      (∀ Y ∈ p.support, Y ⊆ graphEdges G ∧ IsIntegralEdgeCut G Y (edgeThresholdDemands G w)) ∧
      ∀ e, (p.toOuterMeasure {Y | e ∈ Y}).toReal ≤ 8*α*(w e : ℝ) := by
  let α : ℝ := efg n (totalEdgeWeight G w)
  let k := max 1 (positiveArcs G w).card
  have kpos : 0 < k := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  refine edge_uniform_of_small_mass_at_scale hn G w kpos ?_
  change α*smallEdgeMass G w (4*α*(k : ℝ))⁻¹ ≤ 1/4
  by_cases hα : α = 0
  · rw [hα,zero_mul]
    norm_num
  · have apos : 0 < α := lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hα)
    let δ := (4*α*(k : ℝ))⁻¹
    have nonneg : 0 ≤ δ := by dsimp only [δ]; positivity
    have card : ((positiveArcs G w).card : ℝ) ≤ k := Nat.cast_le.mpr (le_max_right _ _)
    have bound := (smallEdgeMass_le_positive_arc_count G w δ nonneg).trans
      (mul_le_mul_of_nonneg_right card nonneg)
    exact (mul_le_mul_of_nonneg_left bound apos.le).trans_eq (by unfold δ; field_simp)

end
end DirectedFlowCutGap.ExactFlowCutGap
