import DirectedFlowCutGap.MeasuredColumnCover
import DirectedFlowCutGap.MeasuredBudgetCoverCandidate

/-! Carry the column charge through repricing and writing the same budgeted
candidate lengths. -/
namespace DirectedFlowCutGap.MeasuredColumnBudgetCandidate

open BinaryFractionalWalkOracle (Adjacency)
open ConcurrentEdgeOracle (Edge)
open RationalEdgeThresholds (Weights)
open RawNonnegativeRational (Code)
open FractionalCover (fuel)
open MeasuredColumnCover (edgeRun vertexRun)

variable {n m : ℕ}

def edgeExtra (n m : ℕ) : ℕ := (fuel (n*n)+1)*MeasuredPathColumn.edgeWork n m

def edge (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (fee mass : Code) : Weights n × ℕ :=
  let prices := MeasuredBudgetPrices.edge c fee mass
  let covered := edgeRun hn A prices.1 P (fuel (n*n))
  let written := MeasuredCoverLengths.edge m covered.stored.best
  (written.1,prices.2+covered.arithmetic+covered.oracleWork+written.2)

theorem edge_preserves (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (fee mass : Code) :
    (edge hn A c P fee mass).1 = (MeasuredBudgetCoverCandidate.edge hn A c P fee mass).1 ∧
    (edge hn A c P fee mass).2 ≤ (MeasuredBudgetCoverCandidate.edge hn A c P fee mass).2+edgeExtra n m := by
  obtain ⟨stored,arithmetic,work⟩ :=
    MeasuredColumnCover.edgeRun_preserves hn A (MeasuredBudgetPrices.edge c fee mass).1 P (fuel (n*n))
  simp only [edge,MeasuredBudgetCoverCandidate.edge,stored,arithmetic,true_and,edgeExtra]
  omega

def vertexExtra (n m : ℕ) : ℕ := (fuel n+1)*MeasuredPathColumn.vertexWork n m

def vertex (hn : 0 < n) (A : Adjacency n) (c : BinaryFractionalRows.Row n)
    (P : Vector (Edge n) m) (fee mass : Code) : BinaryFractionalRows.Row n × ℕ :=
  let prices := MeasuredBudgetPrices.vertex c fee mass
  let covered := vertexRun hn A prices.1 P (fuel n)
  let written := MeasuredCoverLengths.vertex m covered.stored.best
  (written.1,prices.2+covered.arithmetic+covered.oracleWork+written.2)

theorem vertex_preserves (hn : 0 < n) (A : Adjacency n) (c : BinaryFractionalRows.Row n)
    (P : Vector (Edge n) m) (fee mass : Code) :
    (vertex hn A c P fee mass).1 = (MeasuredBudgetCoverCandidate.vertex hn A c P fee mass).1 ∧
    (vertex hn A c P fee mass).2 ≤ (MeasuredBudgetCoverCandidate.vertex hn A c P fee mass).2+vertexExtra n m := by
  obtain ⟨stored,arithmetic,work⟩ :=
    MeasuredColumnCover.vertexRun_preserves hn A (MeasuredBudgetPrices.vertex c fee mass).1 P (fuel n)
  simp only [vertex,MeasuredBudgetCoverCandidate.vertex,stored,arithmetic,true_and,vertexExtra]
  omega

end DirectedFlowCutGap.MeasuredColumnBudgetCandidate
