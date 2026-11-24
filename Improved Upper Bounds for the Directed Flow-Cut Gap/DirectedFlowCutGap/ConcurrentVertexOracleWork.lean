import DirectedFlowCutGap.ConcurrentVertexOracle
import DirectedFlowCutGap.ConcurrentEdgeOracleWork

/-! Account for the binary calls in the joint vertex oracle. Every demand
uses its own source-specific weights and the original path projection. -/
namespace DirectedFlowCutGap.ConcurrentVertexOracleWork

open scoped BigOperators
open BinaryFractionalWalkOracle (Adjacency Candidate shortest)
open ConcurrentVertexOracle (lifted path column)
open ConcurrentEdgeOracle (Edge edge encoded)
open FractionalCoverRawCore (rational)
open FractionalCover (Row value)
open MultiplicityCover (coeff)
open MultiplicityCoverWidths (Fits RowFits ColumnFits)
open RationalEdgeThresholds (cost)
open BinaryFractionalWalkBounds (shortestBound)
open IntegralNetworkFlow

variable {m n : ℕ}

private def call (A : Adjacency n) (y : Row n) (d : Edge n) : Option (Candidate n) × ℕ :=
  shortest (ResidualSearch.Enumeration.fin n) A (cost (encoded (lifted d.1 y))) d.1 d.2

private theorem call_value (A : Adjacency n) (y : Row n) (d : Edge n) :
    (call A y d).1 = path A y d := rfl

private theorem lifted_fits (y : Row n) (s : Fin n) {W : ℕ} (fit : RowFits y W) :
    RowFits (lifted s y) W := by
  intro i
  simp only [lifted,FractionalCover.value_ofFn,FractionalCoverGraphOracle.outgoing]
  split
  · exact MultiplicityCoverWidths.fits_nat (a := 0) (Nat.zero_le _)
  · exact fit _

private theorem call_charge (A : Adjacency n) (y : Row n) (d : Edge n) {W : ℕ}
    (fit : RowFits y W) : (call A y d).2 ≤ shortestBound n (W+1) 2 :=
  BinaryFractionalWalkBounds.shortest_charge (ResidualSearch.Enumeration.fin n) A
    (cost (encoded (lifted d.1 y)))
    (fun e => ConcurrentEdgeCoverWidths.encoded_fits _ (lifted_fits y d.1 fit) e.1 e.2)
    (fun _ => le_rfl) d.1 d.2

def paths (A : Adjacency n) (P : Vector (Edge n) m) (y : Row n) : Vector (Option (Candidate n)) m × ℕ :=
  let cells := Vector.ofFn fun j => call A y (P.get j)
  (cells.map Prod.fst,∑ j : Fin m, (cells.get j).2)

theorem paths_value (A : Adjacency n) (P : Vector (Edge n) m) (y : Row n) :
    (paths A P y).1 = ConcurrentVertexOracle.cells A P y := by
  apply Vector.ext
  intro i hi
  simp only [paths,ConcurrentVertexOracle.cells,Vector.getElem_ofFn,Vector.getElem_map,call_value]

theorem paths_charge (A : Adjacency n) (P : Vector (Edge n) m) (y : Row n) {W : ℕ}
    (fit : RowFits y W) : (paths A P y).2 ≤ m*shortestBound n (W+1) 2 := by
  let cells := Vector.ofFn fun j => call A y (P.get j)
  have each (j : Fin m) : (cells.get j).2 ≤ shortestBound n (W+1) 2 := by
    change cells[j.val].2 ≤ _
    simpa only [cells,Vector.getElem_ofFn,Fin.eta] using call_charge A y (P.get j) fit
  change (∑ j : Fin m, (cells.get j).2) ≤ _
  exact (Finset.sum_le_sum (fun j _ => each j)).trans_eq (by simp)

theorem column_fits (P : Vector (Edge n) m) (cells : Vector (Option (Candidate n)) m) :
    ColumnFits (column P cells) m := by
  intro i
  have h : coeff (column P cells) i ≤ m := by
    simp only [column,coeff,Vector.getElem_ofFn]
    calc
      _ ≤ ∑ _j : Fin m, (1 : ℕ) := by
        apply Finset.sum_le_sum
        intro j _
        split <;> decide
      _ = m := by simp
  exact h.trans Nat.lt_two_pow_self.le

end DirectedFlowCutGap.ConcurrentVertexOracleWork
