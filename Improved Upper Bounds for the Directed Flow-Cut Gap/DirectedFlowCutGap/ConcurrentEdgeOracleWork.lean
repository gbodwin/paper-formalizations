import DirectedFlowCutGap.ConcurrentEdgeCoverWidths
import DirectedFlowCutGap.BinaryFractionalWalkBounds

/-! Retain the established binary shortest-path charges for exactly the
demand cells used by the joint covering oracle. -/
namespace DirectedFlowCutGap.ConcurrentEdgeOracleWork

open scoped BigOperators
open IntegralNetworkFlow
open BinaryFractionalWalkOracle (Adjacency Candidate shortest)
open ConcurrentEdgeOracle (Edge encoded)
open RationalEdgeThresholds (Weights cost)
open FractionalCover (Row)
open ConcurrentEdgeCoverWidths (MatrixFits encoded_fits)
open MultiplicityCoverWidths (RowFits weightWidth)
open BinaryFractionalWalkBounds (shortestBound)

variable {m n : ℕ}

private def calls (A : Adjacency n) (P : Vector (Edge n) m) (y : Row (n*n)) :
    Vector (Option (Candidate n) × ℕ) m :=
  let stored := encoded y
  Vector.ofFn fun d => shortest (ResidualSearch.Enumeration.fin n) A (cost stored) (P.get d).1 (P.get d).2

def measuredPaths (A : Adjacency n) (P : Vector (Edge n) m) (y : Row (n*n)) :
    Vector (Option (Candidate n)) m × ℕ :=
  let reached := calls A P y
  (reached.map Prod.fst,∑ d : Fin m, (reached.get d).2)

theorem paths_eq (A : Adjacency n) (P : Vector (Edge n) m) (y : Row (n*n)) :
    (measuredPaths A P y).1 = ConcurrentEdgeOracle.cells A P y := by
  apply Vector.ext
  intro i hi
  simp only [measuredPaths,calls,ConcurrentEdgeOracle.cells,ConcurrentEdgeOracle.path,Vector.getElem_map,
    Vector.getElem_ofFn]

theorem charge_le (A : Adjacency n) (P : Vector (Edge n) m) (y : Row (n*n)) {W : ℕ}
    (fit : RowFits y W) : (measuredPaths A P y).2 ≤ m*shortestBound n (W+1) 2 := by
  let stored := encoded y
  have hcost (e : Edge n) : BinaryRational.StoredBounded ((cost stored) e).1 (W+1) :=
    encoded_fits y fit e.1 e.2
  have charged (d : Fin m) : ((calls A P y).get d).2 ≤ shortestBound n (W+1) 2 := by
    have h := BinaryFractionalWalkBounds.shortest_charge (ResidualSearch.Enumeration.fin n) A
      (cost stored) hcost (fun _ => le_rfl) (P.get d).1 (P.get d).2
    change ((calls A P y)[d.val]).2 ≤ _
    simpa only [calls,Vector.getElem_ofFn,stored,Fin.eta] using h
  change (∑ d : Fin m, ((calls A P y).get d).2) ≤ _
  exact (Finset.sum_le_sum (fun d _ => charged d)).trans_eq (by simp)

theorem every_round_charge (hn : 0 < n) (A : Adjacency n) (c : Weights n)
    (P : Vector (Edge n) m) {B : ℕ} (fit : MatrixFits c B) (k : ℕ) :
    let prices := ConcurrentEdgeCover.priceRow A c
    let oracle := ConcurrentEdgeOracle.oracle hn A P prices
    let current := (MultiplicityCover.run prices oracle k).weights
    (measuredPaths A P current).2 ≤ m*shortestBound n (weightWidth (n*n) B m k+1) 2 := by
  let prices := ConcurrentEdgeCover.priceRow A c
  let oracle := ConcurrentEdgeOracle.oracle hn A P prices
  have available := MultiplicityCoverWidths.run_fits prices oracle
    (ConcurrentEdgeCoverWidths.priceRow_fits A c fit) (ConcurrentEdgeCoverWidths.oracle_columns hn A P prices) k
  exact charge_le A P _ available.weights

end DirectedFlowCutGap.ConcurrentEdgeOracleWork
