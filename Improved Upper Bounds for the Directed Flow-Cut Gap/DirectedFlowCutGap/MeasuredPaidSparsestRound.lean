import DirectedFlowCutGap.MeasuredPreparedSparsestRound
import DirectedFlowCutGap.MeasuredSparsestTape

/-! Execute both parts of the budgeted sparsest-cut solvers with work
receipts. The original solvers specify the mask and unread tape. -/
namespace DirectedFlowCutGap.MeasuredPaidSparsestRound

open BinaryArithmetic (Bits)
open BinaryFractionalWalkOracle (Adjacency)
open BinaryRational (StoredBounded)
open ConcurrentEdgeOracle (Edge)
open ConcurrentEdgeCoverWidths (MatrixFits)
open RationalEdgeThresholds (Weights)
open RationalSparsestEdgeRound (Mask)
open RetainedGridState (Flags)
open PhysicalCoverAccess (Read)
open Polynomial

variable {n m : ℕ}

def edge (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (extra confidence : ℕ) (bits : Bits) : Read (Mask n × Bits) :=
  MeasuredPreparedSparsestRound.edgeWithRound hn A c P fun D mode =>
    MeasuredSparsestTape.edge A c P D mode extra confidence bits

def vertex (hn : 0 < n) (A : Adjacency n) (c : BinaryFractionalRows.Row n) (P : Vector (Edge n) m)
    (extra confidence : ℕ) (bits : Bits) : Read (Flags n × Bits) :=
  MeasuredPreparedSparsestRound.vertexWithRound hn A c P bits fun D mode =>
    MeasuredSparsestTape.vertex A c P D mode extra confidence bits

theorem edge_value (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (extra confidence : ℕ) (bits : Bits) :
    (edge hn A c P extra confidence bits).1 = AmplifiedBudgetedSparsestEdge.run hn A c P extra confidence bits :=
  MeasuredPreparedSparsestRound.edgeWithRound_value hn A c P _ extra confidence bits
    (fun D mode => MeasuredSparsestTape.edge_value A c P D mode extra confidence bits)

theorem vertex_value (hn : 0 < n) (A : Adjacency n) (c : BinaryFractionalRows.Row n) (P : Vector (Edge n) m)
    (extra confidence : ℕ) (bits : Bits) :
    (vertex hn A c P extra confidence bits).1 = ConcurrentVertexBudgetRound.run hn A c P extra confidence bits :=
  MeasuredPreparedSparsestRound.vertexWithRound_value hn A c P _ extra confidence bits
    (fun D mode => MeasuredSparsestTape.vertex_value A c P D mode extra confidence bits)

noncomputable def edgeWork (p : Polynomial ℕ) (n m B extra confidence : ℕ) : ℕ :=
  MeasuredPreparedSparsestRound.edgeWork n m B+
    MeasuredSparsestTape.edgeWork p n m B (MeasuredPreparedSparsestRound.edgeInputWidth n m B) extra confidence

noncomputable def vertexWork (p : Polynomial ℕ) (n m B extra confidence : ℕ) : ℕ :=
  MeasuredPreparedSparsestRound.vertexWork n m B+
    MeasuredSparsestTape.vertexWork p n m B (MeasuredPreparedSparsestRound.vertexInputWidth n m B) extra confidence

theorem edge_charge (p : Polynomial ℕ)
    (cutoff : ∀ n L T, GuardedCutoffWork.budget n L T ≤ p.eval (n+T))
    (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (extra confidence : ℕ) (bits : Bits) {B : ℕ} (fits : MatrixFits c B) :
    (edge hn A c P extra confidence bits).2 ≤ edgeWork p n m B extra confidence :=
  MeasuredPreparedSparsestRound.edgeWithRound_charge hn A c P _ fits (fun D mode roundFits =>
    MeasuredSparsestTape.edge_charge p cutoff A c P D mode extra confidence bits fits roundFits)

theorem vertex_charge (p : Polynomial ℕ)
    (cutoff : ∀ n L T, GuardedCutoffWork.budget n L T ≤ p.eval (n+T))
    (hn : 0 < n) (A : Adjacency n) (c : BinaryFractionalRows.Row n) (P : Vector (Edge n) m)
    (extra confidence : ℕ) (bits : Bits) {B : ℕ} (fits : ∀ i, StoredBounded (c.get i) B) :
    (vertex hn A c P extra confidence bits).2 ≤ vertexWork p n m B extra confidence :=
  MeasuredPreparedSparsestRound.vertexWithRound_charge hn A c P bits _ fits (fun D mode roundFits =>
    MeasuredSparsestTape.vertex_charge p cutoff A c P D mode extra confidence bits fits roundFits)

end DirectedFlowCutGap.MeasuredPaidSparsestRound
