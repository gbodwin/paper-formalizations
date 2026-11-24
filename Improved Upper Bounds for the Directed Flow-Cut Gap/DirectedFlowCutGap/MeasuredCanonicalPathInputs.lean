import DirectedFlowCutGap.MeasuredBudgetPrices
import DirectedFlowCutGap.MeasuredConcurrentCover

/-! Compute the canonical edge matrices used by the joint path oracles with
binary normalization. Retain each reached normalization and path charge. -/
namespace DirectedFlowCutGap.MeasuredCanonicalPathInputs

open BinaryFractionalWalkOracle (Adjacency Candidate shortest)
open BinaryFractionalWalkBounds (shortestBound)
open FractionalCoverRawCore (RawRow RowBounded decodeRow rational)
open ConcurrentEdgeOracle (Edge edge resource encoded)
open ConcurrentEdgeCoverWidths (MatrixFits)
open RationalEdgeThresholds (Weights cost)
open MeasuredBudgetPrices (tabulate canonical canonicalWork)
open RawNonnegativeRational (Code)
open IntegralNetworkFlow

variable {m n : ℕ}

def matrix (y : RawRow (n*n)) : Weights n × ℕ :=
  tabulate fun u => tabulate fun v => canonical (FractionalCoverRawCore.get y (resource (u,v)))

theorem matrix_value (y : RawRow (n*n)) :
    (matrix y).1 = encoded (decodeRow y) := by
  apply Vector.ext
  intro u hu
  apply Vector.ext
  intro v hv
  simp only [matrix,MeasuredBudgetPrices.tabulate_value,MeasuredBudgetPrices.canonical_value,
    encoded,Vector.getElem_ofFn,FractionalCoverRawCore.decode_value]
  congr 2
  apply congrArg Code.ofNNRat
  apply Subtype.ext
  exact (max_eq_left (FractionalCoverRawCore.rational_nonneg _)).symm

theorem matrix_width (y : RawRow (n*n)) {B : ℕ} (fit : RowBounded y B) :
    MatrixFits (matrix y).1 (B+1) := by
  intro u v
  simp only [matrix,MeasuredBudgetPrices.tabulate_value]
  exact (MeasuredBudgetPrices.canonical_bounds (fit (resource (u,v)))).1

theorem matrix_charge (y : RawRow (n*n)) {B : ℕ} (fit : RowBounded y B) :
    (matrix y).2 ≤ (n*n)*canonicalWork B := by
  rw [Nat.mul_assoc]
  exact MeasuredBudgetPrices.tabulate_charge _ fun u =>
    MeasuredBudgetPrices.tabulate_charge _ fun v => (MeasuredBudgetPrices.canonical_bounds (fit (resource (u,v)))).2

def edgePaths (A : Adjacency n) (P : Vector (Edge n) m) (y : RawRow (n*n)) :
    Vector (Option (Candidate n)) m × ℕ :=
  let a := matrix y
  let calls := tabulate fun j =>
    shortest (ResidualSearch.Enumeration.fin n) A (cost a.1) (P.get j).1 (P.get j).2
  (calls.1,a.2+calls.2)

theorem edgePaths_value (A : Adjacency n) (P : Vector (Edge n) m) (y : RawRow (n*n)) :
    (edgePaths A P y).1 = ConcurrentEdgeOracle.cells A P (decodeRow y) := by
  apply Vector.ext
  intro i hi
  simp only [edgePaths,MeasuredBudgetPrices.tabulate_value,matrix_value,ConcurrentEdgeOracle.cells,
    ConcurrentEdgeOracle.path,Vector.getElem_ofFn]

def edgeWork (n m B : ℕ) : ℕ :=
  (n*n)*canonicalWork B+m*shortestBound n (B+1) 2

theorem edgePaths_charge (A : Adjacency n) (P : Vector (Edge n) m) (y : RawRow (n*n)) {B : ℕ}
    (fit : RowBounded y B) : (edgePaths A P y).2 ≤ edgeWork n m B := by
  let a := matrix y
  have each (j : Fin m) :
      (shortest (ResidualSearch.Enumeration.fin n) A (cost a.1) (P.get j).1 (P.get j).2).2
        ≤ shortestBound n (B+1) 2 :=
    BinaryFractionalWalkBounds.shortest_charge (ResidualSearch.Enumeration.fin n) A (cost a.1)
      (fun e => matrix_width y fit e.1 e.2) (fun _ => le_rfl) (P.get j).1 (P.get j).2
  exact Nat.add_le_add (matrix_charge y fit) (MeasuredBudgetPrices.tabulate_charge _ each)

def lifted (y : RawRow n) (s : Fin n) : RawRow (n*n) :=
  Vector.ofFn fun i =>
    if (edge i).1 = s then Code.zero else FractionalCoverRawCore.get y (edge i).1

theorem lifted_value (y : RawRow n) (s : Fin n) :
    decodeRow (lifted y s) = ConcurrentVertexOracle.lifted s (decodeRow y) := by
  apply Vector.ext
  intro i hi
  simp only [decodeRow,lifted,ConcurrentVertexOracle.lifted,FractionalCoverGraphOracle.outgoing,
    Vector.getElem_ofFn,FractionalCover.value,FractionalCoverRawCore.get]
  split
  · exact FractionalCoverRawCore.rational_zero
  · rfl

theorem lifted_fits (y : RawRow n) (s : Fin n) {B : ℕ} (fit : RowBounded y B) :
    RowBounded (lifted y s) B := by
  intro i
  simp only [lifted,FractionalCoverRawCore.get_ofFn]
  split
  · exact Code.bounded_mono Code.bounded_zero (Nat.zero_le B)
  · exact fit _

def vertexCall (A : Adjacency n) (y : RawRow n) (d : Edge n) : Option (Candidate n) × ℕ :=
  let a := matrix (lifted y d.1)
  let answer := shortest (ResidualSearch.Enumeration.fin n) A (cost a.1) d.1 d.2
  (answer.1,a.2+answer.2)

theorem vertexCall_value (A : Adjacency n) (y : RawRow n) (d : Edge n) :
    (vertexCall A y d).1 = ConcurrentVertexOracle.path A (decodeRow y) d := by
  simp only [vertexCall,matrix_value,lifted_value,ConcurrentVertexOracle.path,ConcurrentEdgeOracle.path]

theorem vertexCall_charge (A : Adjacency n) (y : RawRow n) (d : Edge n) {B : ℕ}
    (fit : RowBounded y B) :
    (vertexCall A y d).2 ≤ (n*n)*canonicalWork B+shortestBound n (B+1) 2 := by
  let row := lifted y d.1
  have derived := lifted_fits y d.1 fit
  have paid := BinaryFractionalWalkBounds.shortest_charge (ResidualSearch.Enumeration.fin n) A
    (cost (matrix row).1) (fun e => matrix_width row derived e.1 e.2)
    (fun _ => le_rfl) d.1 d.2
  exact Nat.add_le_add (matrix_charge row derived) paid

def vertexPaths (A : Adjacency n) (P : Vector (Edge n) m) (y : RawRow n) :
    Vector (Option (Candidate n)) m × ℕ :=
  tabulate fun j => vertexCall A y (P.get j)

theorem vertexPaths_value (A : Adjacency n) (P : Vector (Edge n) m) (y : RawRow n) :
    (vertexPaths A P y).1 = ConcurrentVertexOracle.cells A P (decodeRow y) := by
  apply Vector.ext
  intro i hi
  simp only [vertexPaths,MeasuredBudgetPrices.tabulate_value,vertexCall_value,
    ConcurrentVertexOracle.cells,Vector.getElem_ofFn]

def vertexWork (n m B : ℕ) : ℕ :=
  m*((n*n)*canonicalWork B+shortestBound n (B+1) 2)

theorem vertexPaths_charge (A : Adjacency n) (P : Vector (Edge n) m) (y : RawRow n) {B : ℕ}
    (fit : RowBounded y B) : (vertexPaths A P y).2 ≤ vertexWork n m B :=
  MeasuredBudgetPrices.tabulate_charge _ (fun j => vertexCall_charge A y (P.get j) fit)

end DirectedFlowCutGap.MeasuredCanonicalPathInputs
