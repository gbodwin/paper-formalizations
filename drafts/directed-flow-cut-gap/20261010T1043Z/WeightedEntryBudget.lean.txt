import DirectedFlowCutGap.WeightedFailureBudget
import DirectedFlowCutGap.WeightedEmptyCutDecision
import DirectedFlowCutGap.VertexRounding
import DirectedFlowCutGap.EdgeRounding

/-!
# Original-graph entry branch to the encoded failure tolerance

The premise refers to the actual deterministic empty-cut entry result. The
all-cost factor is used only on the proof side at unit costs. Vertex codes are
the supplied fractions; edge codes mask nonedges to zero, so nonedge matrix
entries never change the original total weight. The tolerance uses the ambient
coordinate count n² for edges, while the graph still has n vertices.

This closes the mathematical entry/budget implication, not the conditional
failure accounting, actual confidence-word construction, or complete runtime.
-/
namespace DirectedFlowCutGap.WeightedEntryBudget
open scoped BigOperators NNReal
open BinaryFractionalWalkOracle WeightedEmptyCutDecision
open WeightedFailureBudget

variable {n : ℕ}

def vertexCodes (w : BinaryFractionalRows.Row n) (i : Fin n) :
    RawNonnegativeRational.Code := BinaryRational.decode (BinaryFractionalRows.get w i)

def edgeCodes (adjacency : Adjacency n) (w : EdgeInput n) (e : Pair n) :
    RawNonnegativeRational.Code :=
  if (adjacent adjacency e.1 e.2).1 then BinaryRational.decode (edgeCost w e).1
  else RawNonnegativeRational.Code.zero

theorem code_real (q : BinaryRational.Fraction) :
    weight (BinaryRational.decode q) = (realValue q : ℝ) := by
  rw [weight_eq_value]
  change ((BinaryRational.decode q).value : ℝ) =
    (((BinaryRational.decode q).value : ℚ) : ℝ)
  exact (Rat.cast_nnratCast (BinaryRational.decode q).value).symm

theorem vertex_code_value (w : BinaryFractionalRows.Row n) (i : Fin n) :
    weight (vertexCodes w i) = (vertexWeights w i : ℝ) :=
  code_real (BinaryFractionalRows.get w i)

theorem edge_code_value (adjacency : Adjacency n) (w : EdgeInput n) (e : Pair n) :
    weight (edgeCodes adjacency w e) =
      (actualEdgeWeight (graph adjacency) (edgeWeights (edgeCost w)) e : ℝ) := by
  by_cases he : (graph adjacency).Adj e.1 e.2
  · have ha := (adjacent_value adjacency e.1 e.2).mpr he
    simp only [edgeCodes,ha,ite_true,actualEdgeWeight_of_adj _ _ he]
    exact code_real (edgeCost w e).1
  · have ha : (adjacent adjacency e.1 e.2).1 ≠ true :=
      fun h => he ((adjacent_value adjacency e.1 e.2).mp h)
    simp [edgeCodes,ha,actualEdgeWeight_of_not_adj _ _ he,
      weight,RawNonnegativeRational.Code.zero]

theorem vertex_codes_bounded (w : BinaryFractionalRows.Row n) (B : ℕ)
    (h : ∀ i, BinaryRational.StoredBounded (BinaryFractionalRows.get w i) B) :
    ∀ i, (vertexCodes w i).Bounded B :=
  fun i => BinaryFractionalRows.stored_raw_bound (h i)

theorem edge_codes_bounded (adjacency : Adjacency n) (w : EdgeInput n) (B : ℕ)
    (h : ∀ e : Pair n, BinaryRational.StoredBounded (edgeCost w e).1 B) :
    ∀ e, (edgeCodes adjacency w e).Bounded B := by
  intro e
  unfold edgeCodes
  split
  · exact BinaryFractionalRows.stored_raw_bound (h e)
  · exact RawNonnegativeRational.Code.bounded_mono
      RawNonnegativeRational.Code.bounded_zero (Nat.zero_le B)

theorem vertex_unit_budget (adjacency : Adjacency n) (w : BinaryFractionalRows.Row n)
    {α : ℝ} (hα : HasVertexRoundingFactor (graph adjacency) (vertexWeights w) α)
    (hentry : (vertexEntry adjacency w).1 = none) :
    1 ≤ α * WeightedFailureBudget.totalWeight (vertexCodes w) := by
  have hempty : ¬IsIntegralCut (graph adjacency) ∅
      (thresholdDemands (graph adjacency) (vertexWeights w)) := by
    intro h
    have hs := (vertexEntry_empty_iff adjacency w).mpr h
    rw [hentry] at hs
    cases hs
  apply nonempty_unit_cost
    (family := {cut | IsIntegralCut (graph adjacency) cut
      (thresholdDemands (graph adjacency) (vertexWeights w))}) hempty
  obtain ⟨cut,hcut,hcost⟩ := hα.real_cost_round (fun _ => 1) (fun _ => by norm_num)
  refine ⟨cut,hcut,?_⟩
  simpa [mwPotential,WeightedFailureBudget.totalWeight,vertex_code_value] using hcost

theorem edge_unit_budget (adjacency : Adjacency n) (w : EdgeInput n)
    {α : ℝ} (hα : HasEdgeRoundingFactor (graph adjacency) (edgeWeights (edgeCost w)) α)
    (hentry : (edgeEntry adjacency w).1 = none) :
    1 ≤ α * WeightedFailureBudget.totalWeight (edgeCodes adjacency w) := by
  have hempty : ¬IsIntegralEdgeCut (graph adjacency) ∅
      (edgeThresholdDemands (graph adjacency) (edgeWeights (edgeCost w))) := by
    intro h
    have hs := (edgeEntry_empty_iff adjacency w).mpr h
    rw [hentry] at hs
    cases hs
  apply nonempty_unit_cost
    (family := {cut | cut ⊆ graphEdges (graph adjacency) ∧
      IsIntegralEdgeCut (graph adjacency) cut
        (edgeThresholdDemands (graph adjacency) (edgeWeights (edgeCost w)))})
    (fun h => hempty h.2)
  obtain ⟨cut,hcut,hcost⟩ := hα.real_cost_round (fun _ => 1) (fun _ => by norm_num)
  refine ⟨cut,hcut,?_⟩
  simpa [mwPotential,WeightedFailureBudget.totalWeight,edge_code_value] using hcost

/-- The tolerance depends on original input width and vertex count only. -/
theorem vertex_tolerance (adjacency : Adjacency n) (w : BinaryFractionalRows.Row n)
    (B : ℕ) (hB : ∀ i, BinaryRational.StoredBounded (BinaryFractionalRows.get w i) B)
    {α : ℝ} (hα : HasVertexRoundingFactor (graph adjacency) (vertexWeights w) α)
    (hentry : (vertexEntry adjacency w).1 = none)
    (i : Fin n) (hi : 0 < (vertexWeights w i : ℝ)) :
    tolerance n B ≤ α * (vertexWeights w i : ℝ) := by
  have h := tolerance_le_scaled_weight (vertexCodes w) B (vertex_codes_bounded w B hB)
    hα.nonneg (vertex_unit_budget adjacency w hα hentry) i
    (by simpa only [vertex_code_value] using hi)
  simpa only [Fintype.card_fin,vertex_code_value] using h

/-- n² is an ambient count, not a replacement of the graph's vertex count or W. -/
theorem edge_tolerance (adjacency : Adjacency n) (w : EdgeInput n) (B : ℕ)
    (hB : ∀ e : Pair n, BinaryRational.StoredBounded (edgeCost w e).1 B)
    {α : ℝ} (hα : HasEdgeRoundingFactor (graph adjacency) (edgeWeights (edgeCost w)) α)
    (hentry : (edgeEntry adjacency w).1 = none)
    (e : Pair n) (he : (graph adjacency).Adj e.1 e.2)
    (hw : 0 < (edgeWeights (edgeCost w) e : ℝ)) :
    tolerance (n*n) B ≤ α * (edgeWeights (edgeCost w) e : ℝ) := by
  have hi : 0 < weight (edgeCodes adjacency w e) := by
    simpa only [edge_code_value,actualEdgeWeight_of_adj _ _ he] using hw
  have h := tolerance_le_scaled_weight (edgeCodes adjacency w) B
    (edge_codes_bounded adjacency w B hB) hα.nonneg
    (edge_unit_budget adjacency w hα hentry) e hi
  simpa only [Fintype.card_prod,Fintype.card_fin,edge_code_value,
    actualEdgeWeight_of_adj _ _ he] using h

end DirectedFlowCutGap.WeightedEntryBudget
