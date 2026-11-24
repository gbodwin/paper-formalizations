import DirectedFlowCutGap.MeasuredCanonicalCover
import DirectedFlowCutGap.MeasuredCoverLengths

/-! Connect measured repricing, covering, and final length readout for a
single budget pair. These steps preserve the exact canonical output. -/
namespace DirectedFlowCutGap.MeasuredBudgetCoverCandidate

open BinaryFractionalWalkOracle (Adjacency)
open ConcurrentEdgeOracle (Edge)
open RationalEdgeThresholds (Weights)
open ConcurrentEdgeCoverWidths (MatrixFits)
open BinaryRational (StoredBounded)
open RawNonnegativeRational (Code)
open FractionalCover (fuel)
open MultiplicityCoverWidths (weightWidth normalizedWidth)
open MeasuredCanonicalCover (edgeRun vertexRun arithmeticBound edgeOracleBound vertexOracleBound)
open MeasuredBudgetPrices (cellWork cell_bounds tabulate_value)

variable {n m : ℕ}

def edge (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (fee mass : Code) : Weights n × ℕ :=
  let prices := MeasuredBudgetPrices.edge c fee mass
  let covered := edgeRun hn A prices.1 P (fuel (n*n))
  let written := MeasuredCoverLengths.edge m covered.stored.best
  (written.1,prices.2+covered.arithmetic+covered.oracleWork+written.2)

theorem edge_value (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (fee mass : Code) :
    (edge hn A c P fee mass).1 = ConcurrentEdgeMassBudget.solve hn A c P fee.value mass.value := by
  let repriced := MeasuredBudgetPrices.edge c fee mass
  have same := congrArg MultiplicityCover.State.best
    (MeasuredCanonicalCover.edgeRun_value hn A repriced.1 P (fuel (n*n)))
  dsimp only [MeasuredMultiplicityCover.decoded] at same
  change (MeasuredCoverLengths.edge m (edgeRun hn A repriced.1 P (fuel (n*n))).stored.best).1 = _
  rw [MeasuredCoverLengths.edge_value,same]
  simp only [repriced,MeasuredBudgetPrices.edge_value,ConcurrentEdgeMassBudget.solve,
    ConcurrentEdgeCover.solve,ConcurrentEdgeCover.base,MultiplicityCover.solve]

def edgeWork (n m B F M : ℕ) : ℕ :=
  let r := n*n
  let k := fuel r
  let W := B+F+M+2
  r*cellWork B F M+arithmeticBound r m W k+edgeOracleBound n m W k+
    MeasuredCoverLengths.work r m (normalizedWidth r m (weightWidth r W m k))

theorem edge_charge (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (fee mass : Code) {B F M : ℕ} (input : MatrixFits c B)
    (feeFit : fee.Bounded F) (massFit : mass.Bounded M) :
    (edge hn A c P fee mass).2 ≤ edgeWork n m B F M := by
  let prices := MeasuredBudgetPrices.edge c fee mass
  have fit : MatrixFits prices.1 (B+F+M+2) := by
    intro u v
    simp only [prices,MeasuredBudgetPrices.edge,tabulate_value]
    exact (cell_bounds ((c.get u).get v) fee mass (input u v) feeFit massFit).1
  obtain ⟨fields,arithmetic,oracle⟩ := MeasuredCanonicalCover.edgeRun_bounds hn A prices.1 P fit (fuel (n*n))
  have readout := MeasuredCoverLengths.edge_charge m _ fields.best
  exact Nat.add_le_add (Nat.add_le_add
    (Nat.add_le_add (MeasuredBudgetPrices.edge_charge c fee mass input feeFit massFit) arithmetic) oracle) readout

def vertex (hn : 0 < n) (A : Adjacency n) (c : BinaryFractionalRows.Row n)
    (P : Vector (Edge n) m) (fee mass : Code) : BinaryFractionalRows.Row n × ℕ :=
  let prices := MeasuredBudgetPrices.vertex c fee mass
  let covered := vertexRun hn A prices.1 P (fuel n)
  let written := MeasuredCoverLengths.vertex m covered.stored.best
  (written.1,prices.2+covered.arithmetic+covered.oracleWork+written.2)

theorem vertex_value (hn : 0 < n) (A : Adjacency n) (c : BinaryFractionalRows.Row n)
    (P : Vector (Edge n) m) (fee mass : Code) :
    (vertex hn A c P fee mass).1 = ConcurrentVertexBudget.candidate hn A c P fee.value mass.value := by
  let repriced := MeasuredBudgetPrices.vertex c fee mass
  have same := congrArg MultiplicityCover.State.best
    (MeasuredCanonicalCover.vertexRun_value hn A repriced.1 P (fuel n))
  dsimp only [MeasuredMultiplicityCover.decoded] at same
  change (MeasuredCoverLengths.vertex m (vertexRun hn A repriced.1 P (fuel n)).stored.best).1 = _
  rw [MeasuredCoverLengths.vertex_value,same]
  simp only [repriced,MeasuredBudgetPrices.vertex_value,ConcurrentVertexBudget.candidate,
    ConcurrentVertexCover.solve,ConcurrentVertexCover.base,MultiplicityCover.solve]

def vertexWork (n m B F M : ℕ) : ℕ :=
  let k := fuel n
  let W := B+F+M+2
  n*cellWork B F M+arithmeticBound n m W k+vertexOracleBound n m W k+
    MeasuredCoverLengths.work n m (normalizedWidth n m (weightWidth n W m k))

theorem vertex_charge (hn : 0 < n) (A : Adjacency n) (c : BinaryFractionalRows.Row n)
    (P : Vector (Edge n) m) (fee mass : Code) {B F M : ℕ}
    (input : ∀ i, StoredBounded (c.get i) B) (feeFit : fee.Bounded F) (massFit : mass.Bounded M) :
    (vertex hn A c P fee mass).2 ≤ vertexWork n m B F M := by
  let prices := MeasuredBudgetPrices.vertex c fee mass
  have fit (i : Fin n) : StoredBounded (prices.1.get i) (B+F+M+2) := by
    change StoredBounded prices.1[i.val] _
    simp only [prices,MeasuredBudgetPrices.vertex,tabulate_value]
    exact (cell_bounds (c.get i) fee mass (input i) feeFit massFit).1
  obtain ⟨fields,arithmetic,oracle⟩ := MeasuredCanonicalCover.vertexRun_bounds hn A prices.1 P fit (fuel n)
  have readout := MeasuredCoverLengths.vertex_charge m _ fields.best
  exact Nat.add_le_add (Nat.add_le_add
    (Nat.add_le_add (MeasuredBudgetPrices.vertex_charge c fee mass input feeFit massFit) arithmetic) oracle) readout

end DirectedFlowCutGap.MeasuredBudgetCoverCandidate
