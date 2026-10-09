import DirectedFlowCutGap.EdgeModel
import DirectedFlowCutGap.ZeroWeights

/-!
# Actual directed edge rounding factors

An all-cost interface for actual threshold-demand edge cuts, together with the
real-valued cost oracle used by finite multiplicative-weights sampling. Values
on nonedges are masked out of the fractional objective, and all returned cut
sets consist of actual edges. No main asymptotic or runtime claim is made here.
-/

namespace DirectedFlowCutGap
noncomputable section
open scoped BigOperators NNReal ENNReal
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An all-cost rounding factor for actual directed edge-threshold demands. -/
structure HasEdgeRoundingFactor (G : Digraph V) (w : V × V → ℝ≥0) (α : ℝ) : Prop where
  nonneg : 0 ≤ α
  round : ∀ c : V × V → ℝ≥0, ∃ X : Finset (V × V),
    X ⊆ graphEdges G ∧ IsIntegralEdgeCut G X (edgeThresholdDemands G w) ∧
      (edgeCutCost G c X : ℝ) ≤ α * (weightedEdgeCost G c w : ℝ)

/-- Nonedges have zero fractional mass in the ambient ordered-pair space. -/
def actualEdgeWeight (G : Digraph V) (w : V × V → ℝ≥0) (e : V × V) : ℝ≥0 :=
  if G.Adj e.1 e.2 then w e else 0

omit [Fintype V] [DecidableEq V] in
@[simp] theorem actualEdgeWeight_of_adj (G : Digraph V) (w : V × V → ℝ≥0)
    {e : V × V} (he : G.Adj e.1 e.2) : actualEdgeWeight G w e = w e := by
  simp [actualEdgeWeight, he]

omit [Fintype V] [DecidableEq V] in
@[simp] theorem actualEdgeWeight_of_not_adj (G : Digraph V) (w : V × V → ℝ≥0)
    {e : V × V} (he : ¬G.Adj e.1 e.2) : actualEdgeWeight G w e = 0 := by
  simp [actualEdgeWeight, he]

omit [DecidableEq V] in
/-- On actual edge sets the edge cut objective is exactly the usual finite sum. -/
theorem edgeCutCost_eq_sum_of_subset (G : Digraph V) (c : V × V → ℝ≥0)
    {X : Finset (V × V)} (hX : X ⊆ graphEdges G) :
    edgeCutCost G c X = ∑ e ∈ X, c e := by
  unfold edgeCutCost
  rw [Finset.filter_eq_self.mpr (fun e he => (mem_graphEdges G e).mp (hX he))]

omit [DecidableEq V] in
/-- The original fractional edge objective equals the masked ambient potential. -/
theorem coe_weightedEdgeCost_eq_mwPotential (G : Digraph V)
    (c w : V × V → ℝ≥0) :
    (weightedEdgeCost G c w : ℝ) = mwPotential
      (fun e => (actualEdgeWeight G w e : ℝ)) (fun e => (c e : ℝ)) := by
  simp only [weightedEdgeCost, graphEdges, Finset.sum_filter, NNReal.coe_sum,
    mwPotential, actualEdgeWeight]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : G.Adj e.1 e.2 <;> simp [he]

/-- The factor supplies an actual real-valued oracle for every nonnegative
cost vector, including arbitrary values on nonedges and zero-cost edges. -/
theorem HasEdgeRoundingFactor.real_cost_round {G : Digraph V} {w : V × V → ℝ≥0}
    {α : ℝ} (h : HasEdgeRoundingFactor G w α)
    (c : V × V → ℝ) (hc : ∀ e, 0 ≤ c e) :
    ∃ X : Finset (V × V), (X ⊆ graphEdges G ∧
      IsIntegralEdgeCut G X (edgeThresholdDemands G w)) ∧
      (∑ e ∈ X, c e) ≤ α * mwPotential (fun e => (actualEdgeWeight G w e : ℝ)) c := by
  let cNN : V × V → ℝ≥0 := fun e => NNReal.mk (c e) (hc e)
  obtain ⟨X, hX, hvalid, hcost⟩ := h.round cNN
  refine ⟨X, ⟨hX, hvalid⟩, ?_⟩
  rw [edgeCutCost_eq_sum_of_subset G cNN hX,
    coe_weightedEdgeCost_eq_mwPotential] at hcost
  simpa [cNN] using hcost

end
end DirectedFlowCutGap
