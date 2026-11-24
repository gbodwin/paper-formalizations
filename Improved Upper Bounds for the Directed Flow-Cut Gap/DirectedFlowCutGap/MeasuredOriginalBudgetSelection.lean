import DirectedFlowCutGap.MeasuredGraphBudgetGrid
import DirectedFlowCutGap.MeasuredBudgetPlanSelection

/-! From the original typed prices through geometric budgets and the final
plan selection. The charges cover the named arithmetic and oracle work. -/
namespace DirectedFlowCutGap.MeasuredOriginalBudgetSelection

open scoped NNRat
open BinaryFractionalWalkOracle (Adjacency)
open BinaryRational (StoredBounded)
open ConcurrentEdgeOracle (Edge)
open ConcurrentEdgeCoverWidths (MatrixFits)
open MeasuredSparsityScore (harmonic_value harmonic_bounds)
open MeasuredSparsityPlans (ScoredRow decode minimum)
open MeasuredBudgetPlanSelection (collect_minimum_value paid_selection selectionWork)
open RationalEdgeThresholds (Weights)
open RawNonnegativeRational (Code)

variable {n m : ℕ}

def candidates {α : Type*} (solve : Code → Code → α × ℕ) (pairs : List (Code × Code)) : List α × ℕ :=
  let reached := pairs.map fun pair => solve pair.1 pair.2
  (reached.map Prod.fst,(reached.map Prod.snd).sum)

private theorem candidates_value {α : Type*} (solve : Code → Code → α × ℕ) (old : ℚ≥0 → ℚ≥0 → α)
    (pairs : List (Code × Code)) (read : ∀ p q, (solve p q).1 = old p.value q.value) :
    (candidates solve pairs).1 = (pairs.map MeasuredGraphBudgetGrid.decode).map (fun p => old p.1 p.2) := by
  simp only [candidates,List.map_map,Function.comp_def,MeasuredGraphBudgetGrid.decode,read]

private theorem candidates_charge {α : Type*} (solve : Code → Code → α × ℕ)
    (pairs : List (Code × Code)) {W : ℕ} (fits : ∀ p ∈ pairs, (solve p.1 p.2).2 ≤ W) :
    (candidates solve pairs).2 ≤ pairs.length*W := by
  induction pairs with
  | nil => simp [candidates]
  | cons p ps ih =>
    have current := fits p List.mem_cons_self
    have tail := ih (fun q hq => fits q (List.mem_cons_of_mem _ hq))
    simpa only [candidates,List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul,Nat.add_comm] using
      Nat.add_le_add current tail

private def edgeBatch (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m) :
    (List (Weights n) × ℕ) × ℕ :=
  let grid := MeasuredGraphBudgetGrid.edge A c m
  (candidates (MeasuredBudgetCoverCandidate.edge hn A c P) grid.1,grid.2)

def edgeCandidates (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m) :
    List (Weights n) × ℕ := (edgeBatch hn A c P).1

theorem edgeCandidates_value (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m) :
    (edgeCandidates hn A c P).1 = ConcurrentEdgeBudgetGrid.candidates hn A c P := by
  dsimp only [edgeCandidates,edgeBatch]
  rw [candidates_value _ (ConcurrentEdgeMassBudget.solve hn A c P) _
    (MeasuredBudgetCoverCandidate.edge_value hn A c P),MeasuredGraphBudgetGrid.edge_value]
  rfl

private def vertexBatch (hn : 0 < n) (A : Adjacency n) (c : BinaryFractionalRows.Row n)
    (P : Vector (Edge n) m) : (List (BinaryFractionalRows.Row n) × ℕ) × ℕ :=
  let grid := MeasuredGraphBudgetGrid.vertex c m
  (candidates (MeasuredBudgetCoverCandidate.vertex hn A c P) grid.1,grid.2)

def vertexCandidates (hn : 0 < n) (A : Adjacency n) (c : BinaryFractionalRows.Row n)
    (P : Vector (Edge n) m) : List (BinaryFractionalRows.Row n) × ℕ := (vertexBatch hn A c P).1

theorem vertexCandidates_value (hn : 0 < n) (A : Adjacency n) (c : BinaryFractionalRows.Row n)
    (P : Vector (Edge n) m) : (vertexCandidates hn A c P).1 = ConcurrentVertexBudgetGrid.candidates hn A c P := by
  dsimp only [vertexCandidates,vertexBatch]
  rw [candidates_value _ (ConcurrentVertexBudget.candidate hn A c P) _
    (MeasuredBudgetCoverCandidate.vertex_value hn A c P),MeasuredGraphBudgetGrid.vertex_value]
  rfl

def edge (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m) :
    Option (ScoredRow (Weights n)) × ℕ :=
  let batch := edgeBatch hn A c P
  let h := MeasuredSparsityScore.harmonic m
  let plans := MeasuredBudgetPlanSelection.collect batch.1.1 (fun w => MeasuredSparsityPlans.edgePlan A c w m h.1)
  let best := minimum plans.1
  (best.1,batch.2+batch.1.2+h.2+plans.2+best.2)

theorem edge_value (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m) :
    (edge hn A c P).1.map (decode ConcurrentEdgeBudgetSelection.Plan.mk) = ConcurrentEdgeBudgetSelection.choose hn A c P := by
  have same : (edgeBatch hn A c P).1.1 = ConcurrentEdgeBudgetGrid.candidates hn A c P :=
    edgeCandidates_value hn A c P
  simp only [edge,ConcurrentEdgeBudgetSelection.choose,same]
  exact collect_minimum_value _ _ _ _ _ (fun _ _ _ => rfl)
    (fun w => MeasuredSparsityPlans.edgePlan_value A c w m _ (harmonic_value m))

def edgeCount (n m B : ℕ) : ℕ := (n*n*B+(m+n*n*(B+1))+3)*(m+n*2+3)

def edgeWork (n m B : ℕ) : ℕ :=
  let K := edgeCount n m B
  let W := ConcurrentEdgeBudgetWidths.candidateWidth n m B
  MeasuredGraphBudgetGrid.edgeWork n m B+
    K*MeasuredBudgetCoverCandidate.edgeWork n m B
      (ConcurrentEdgeBudgetWidths.priceWidth n m B) (ConcurrentEdgeBudgetWidths.massWidth n m)+
    selectionWork (n*n) n m B W K

theorem edge_charge (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    {B : ℕ} (prices : MatrixFits c B) : (edge hn A c P).2 ≤ edgeWork n m B := by
  let pairs := (MeasuredGraphBudgetGrid.edge A c m).1
  let ys := edgeCandidates hn A c P
  have pairCount : pairs.length ≤ edgeCount n m B := by
    have same := congrArg List.length (MeasuredGraphBudgetGrid.edge_value A c m)
    simp only [List.length_map] at same
    rw [show pairs.length = _ from same]
    exact ConcurrentEdgeBudgetWidths.pair_count A c m prices
  have shape : ys.1.length ≤ edgeCount n m B := by
    simpa only [ys,edgeCandidates,edgeBatch,candidates,List.length_map,pairs] using pairCount
  have spent := (candidates_charge (MeasuredBudgetCoverCandidate.edge hn A c P) pairs (fun p inside => by
    obtain ⟨f,u⟩ := MeasuredGraphBudgetGrid.edge_fields A c m prices inside
    exact MeasuredBudgetCoverCandidate.edge_charge hn A c P _ _ prices f u)).trans
      (Nat.mul_le_mul_right _ pairCount)
  have select := paid_selection ys.1 (fun w => MeasuredSparsityPlans.edgePlan A c w m (MeasuredSparsityScore.harmonic m).1)
    shape (fun w inside => MeasuredSparsityPlans.edgePlan_bounds A c w m _ prices
      (ConcurrentEdgeBudgetWidths.candidate_fits hn A c P prices (edgeCandidates_value hn A c P ▸ inside))
      (harmonic_bounds m).1)
  simpa only [edge,edgeWork,ys,edgeCandidates,edgeBatch,pairs,Nat.add_assoc] using
    Nat.add_le_add (Nat.add_le_add (MeasuredGraphBudgetGrid.edge_charge A c m prices) spent) select

def vertex (hn : 0 < n) (A : Adjacency n) (c : BinaryFractionalRows.Row n) (P : Vector (Edge n) m) :
    Option (ScoredRow (BinaryFractionalRows.Row n)) × ℕ :=
  let batch := vertexBatch hn A c P
  let h := MeasuredSparsityScore.harmonic m
  let plans := MeasuredBudgetPlanSelection.collect batch.1.1 (fun w => MeasuredSparsityPlans.vertexPlan c w m h.1)
  let best := minimum plans.1
  (best.1,batch.2+batch.1.2+h.2+plans.2+best.2)

theorem vertex_value (hn : 0 < n) (A : Adjacency n) (c : BinaryFractionalRows.Row n) (P : Vector (Edge n) m) :
    (vertex hn A c P).1.map (decode ConcurrentVertexBudgetSelection.Plan.mk) =
      ConcurrentVertexBudgetSelection.choose hn A c P := by
  have same : (vertexBatch hn A c P).1.1 = ConcurrentVertexBudgetGrid.candidates hn A c P :=
    vertexCandidates_value hn A c P
  simp only [vertex,ConcurrentVertexBudgetSelection.choose,same]
  exact collect_minimum_value _ _ _ _ _ (fun _ _ _ => rfl)
    (fun w => MeasuredSparsityPlans.vertexPlan_value c w m _ (harmonic_value m))

def vertexWork (n m B : ℕ) : ℕ :=
  let K := MeasuredBudgetCandidateLists.vertexCount n m B
  let W := MeasuredBudgetPlanSelection.vertexWidth n m B
  MeasuredGraphBudgetGrid.vertexWork n m B+
    K*MeasuredBudgetCoverCandidate.vertexWork n m B
      (MeasuredBudgetCandidateLists.vertexPriceWidth n m B) (MeasuredBudgetCandidateLists.vertexMassWidth n m)+
    selectionWork n n m B W K

theorem vertex_charge (hn : 0 < n) (A : Adjacency n) (c : BinaryFractionalRows.Row n)
    (P : Vector (Edge n) m) {B : ℕ} (prices : ∀ i, StoredBounded (c.get i) B) : (vertex hn A c P).2 ≤ vertexWork n m B := by
  let pairs := (MeasuredGraphBudgetGrid.vertex c m).1
  let ys := vertexCandidates hn A c P
  have pairCount : pairs.length ≤ MeasuredBudgetCandidateLists.vertexCount n m B := by
    have same := congrArg List.length (MeasuredGraphBudgetGrid.vertex_value c m)
    simp only [List.length_map] at same
    rw [show pairs.length = _ from same]
    exact MeasuredBudgetCandidateLists.vertex_pair_count c m prices
  have shape : ys.1.length ≤ MeasuredBudgetCandidateLists.vertexCount n m B := by
    simpa only [ys,vertexCandidates,vertexBatch,candidates,List.length_map,pairs] using pairCount
  have spent := (candidates_charge (MeasuredBudgetCoverCandidate.vertex hn A c P) pairs (fun p inside => by
    obtain ⟨f,u⟩ := MeasuredGraphBudgetGrid.vertex_fields c m prices inside
    exact MeasuredBudgetCoverCandidate.vertex_charge hn A c P _ _ prices f u)).trans
      (Nat.mul_le_mul_right _ pairCount)
  have select := paid_selection ys.1 (fun w => MeasuredSparsityPlans.vertexPlan c w m (MeasuredSparsityScore.harmonic m).1)
    shape (fun w inside => MeasuredSparsityPlans.vertexPlan_bounds c w m _ prices
      (MeasuredBudgetPlanSelection.vertex_candidate_fits hn A c P prices (vertexCandidates_value hn A c P ▸ inside))
      (harmonic_bounds m).1)
  simpa only [vertex,vertexWork,ys,vertexCandidates,vertexBatch,pairs,Nat.add_assoc] using
    Nat.add_le_add (Nat.add_le_add (MeasuredGraphBudgetGrid.vertex_charge c m prices) spent) select

end DirectedFlowCutGap.MeasuredOriginalBudgetSelection
