import DirectedFlowCutGap.MeasuredColumnBudgetSelection
import DirectedFlowCutGap.MeasuredBudgetedSparsestRound

/-! The column-counted optimizer supplies the same original graph cut and
unread suffix. The reported charge still concerns the optimizer. -/
namespace DirectedFlowCutGap.MeasuredColumnSparsestRound

open BinaryArithmetic (Bits)
open BinaryFractionalWalkOracle (Adjacency)
open BinaryRational (StoredBounded)
open ConcurrentEdgeOracle (Edge)
open ConcurrentEdgeCoverWidths (MatrixFits)
open RationalEdgeThresholds (Weights)
open ChargedVertexModes (Mode)
open RationalSparsestEdgeRound (Mask)
open RetainedGridState (Flags)

variable {n m : ℕ}

private def edgePrepare (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m) :
    Option (Weights n × Mode) × ℕ :=
  match ConcurrentEdgeZeroPrices.detect A c P with
  | some _ => (some (ConcurrentEdgeZeroPrices.freeLength c m,.mass),0)
  | none =>
    let result := MeasuredColumnBudgetSelection.edge hn A c P
    (result.1.map (fun z => (z.row,z.scored.mode)),result.2)

private theorem edgePrepare_value (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m) :
    (edgePrepare hn A c P).1 = ConcurrentEdgeBudgetRound.prepare hn A c P := by
  have same := (MeasuredColumnBudgetSelection.edge_preserves hn A c P).1
  have plan := congrArg (Option.map (fun q : ConcurrentEdgeBudgetSelection.Plan n => (q.lengths,q.mode)))
    (MeasuredOriginalBudgetSelection.edge_value hn A c P)
  simp only [Option.map_map,Function.comp_def,MeasuredSparsityPlans.decode] at plan
  cases found : ConcurrentEdgeZeroPrices.detect A c P
  · simpa only [edgePrepare,ConcurrentEdgeBudgetRound.prepare,found,same] using plan
  · simp only [edgePrepare,ConcurrentEdgeBudgetRound.prepare,found]

def edge (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (extra confidence : ℕ) (bits : Bits) : Option (Mask n × Bits) × ℕ :=
  let prepared := edgePrepare hn A c P
  let cut := prepared.1.bind fun (w,mode) =>
    match RationalSparsestEdgeThreshold.choose A w P with
    | .threshold _ τ => AmplifiedSparsestEdgeTape.round A c P
        (RationalSparsestEdgeRound.scaled A w c τ) mode extra confidence bits
    | _ => none
  (cut,prepared.2)

theorem edge_value (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (extra confidence : ℕ) (bits : Bits) :
    (edge hn A c P extra confidence bits).1 = AmplifiedBudgetedSparsestEdge.run hn A c P extra confidence bits := by
  simp only [edge,edgePrepare_value,AmplifiedBudgetedSparsestEdge.run]
  congr 1

theorem edge_optimizer_charge (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (extra confidence : ℕ) (bits : Bits) {B : ℕ} (width : MatrixFits c B) :
    (edge hn A c P extra confidence bits).2 ≤ MeasuredColumnBudgetSelection.edgeWork n m B := by
  change (edgePrepare hn A c P).2 ≤ _
  cases found : ConcurrentEdgeZeroPrices.detect A c P
  · simpa only [edgePrepare,found] using MeasuredColumnBudgetSelection.edge_charge hn A c P width
  · simp only [edgePrepare,found,Nat.zero_le]

def vertex (hn : 0 < n) (A : Adjacency n) (c : BinaryFractionalRows.Row n) (P : Vector (Edge n) m)
    (extra confidence : ℕ) (bits : Bits) : Option (Flags n × Bits) × ℕ :=
  match ConcurrentVertexBudget.freeDemand A c P with
  | some _ => (some (ConcurrentVertexBudget.freeMask c,bits),0)
  | none =>
    let result := MeasuredColumnBudgetSelection.vertex hn A c P
    let cut := result.1.bind fun z =>
      match RationalSparsestVertexThreshold.choose A z.row P with
      | .threshold _ τ => AmplifiedSparsestVertexTape.round A c P
          (RationalSparsestVertexRound.scaled A z.row c τ) z.scored.mode extra confidence bits
      | _ => none
    (cut,result.2)

theorem vertex_value (hn : 0 < n) (A : Adjacency n) (c : BinaryFractionalRows.Row n) (P : Vector (Edge n) m)
    (extra confidence : ℕ) (bits : Bits) :
    (vertex hn A c P extra confidence bits).1 = ConcurrentVertexBudgetRound.run hn A c P extra confidence bits := by
  cases found : ConcurrentVertexBudget.freeDemand A c P
  · simp only [vertex,ConcurrentVertexBudgetRound.run,found,(MeasuredColumnBudgetSelection.vertex_preserves hn A c P).1]
    rw [← MeasuredOriginalBudgetSelection.vertex_value hn A c P]
    simp only [Option.bind_map,Function.comp_def,MeasuredSparsityPlans.decode]
    congr 1
  · simp only [vertex,ConcurrentVertexBudgetRound.run,found]

theorem vertex_optimizer_charge (hn : 0 < n) (A : Adjacency n) (c : BinaryFractionalRows.Row n)
    (P : Vector (Edge n) m) (extra confidence : ℕ) (bits : Bits) {B : ℕ}
    (width : ∀ i, StoredBounded (c.get i) B) :
    (vertex hn A c P extra confidence bits).2 ≤ MeasuredColumnBudgetSelection.vertexWork n m B := by
  cases found : ConcurrentVertexBudget.freeDemand A c P
  · simpa only [vertex,found] using MeasuredColumnBudgetSelection.vertex_charge hn A c P width
  · simp only [vertex,found,Nat.zero_le]

end DirectedFlowCutGap.MeasuredColumnSparsestRound
