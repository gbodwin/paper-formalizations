import DirectedFlowCutGap.MeasuredMultiplicityCoverBounds
import DirectedFlowCutGap.MeasuredMultiplicityPivot
import DirectedFlowCutGap.ConcurrentVertexOracleWork
import DirectedFlowCutGap.ConcurrentVertexCover

/-! Measured covering iterations on the actual typed graph inputs. The
reported work retains the binary state arithmetic, shortest-path calls and
bottleneck scoring. Path projection, storage and assembly are separate. -/
namespace DirectedFlowCutGap.MeasuredConcurrentCover

open BinaryFractionalWalkOracle (Adjacency Candidate decodeCost)
open RationalEdgeThresholds (Weights cost)
open ConcurrentEdgeOracle (Edge edge)
open ConcurrentEdgeCoverWidths (MatrixFits)
open MultiplicityCoverWidths (RowFits ColumnFits weightWidth)
open MeasuredMultiplicityCover (Execution MeasuredOracle decoded Refines run)
open MeasuredMultiplicityCoverBounds (startWork advanceWork)
open MeasuredMultiplicityPivot (choose work)
open FractionalCoverRawCore (RawRow RowBounded get decodeRow rational)
open RawNonnegativeRational (Code)
open BinaryFractionalWalkBounds (shortestBound)

variable {m n r : ℕ}

private theorem canonical_width (y : RawRow r) {W : ℕ} (fit : RowBounded y W) : RowFits (decodeRow y) W := by
  intro i
  rw [FractionalCoverRawCore.decode_value]
  exact MultiplicityCoverWidths.fits_code (fit i)

def edgePrices (A : Adjacency n) (c : Weights n) : RawRow (n*n) :=
  Vector.ofFn fun i =>
    let e := edge i
    if A[e.1.val][e.2.val] then decodeCost (cost c) e else Code.one

theorem edgePrices_value (A : Adjacency n) (c : Weights n) :
    decodeRow (edgePrices A c) = ConcurrentEdgeCover.priceRow A c := by
  apply Vector.ext
  intro i hi
  simp only [edgePrices,decodeRow,FractionalCoverRawCore.get,ConcurrentEdgeCover.priceRow,Vector.getElem_ofFn]
  split
  · rfl
  · exact FractionalCoverRawCore.rational_one

theorem edgePrices_fits (A : Adjacency n) (c : Weights n) {B : ℕ} (fit : MatrixFits c B) :
    RowBounded (edgePrices A c) B := by
  intro i
  simp only [edgePrices,FractionalCoverRawCore.get_ofFn]
  split
  · exact BinaryFractionalRows.stored_raw_bound (fit (edge i).1 (edge i).2)
  · exact Code.bounded_mono Code.bounded_one (Nat.zero_le B)

def vertexPrices (c : BinaryFractionalRows.Row n) : RawRow n :=
  Vector.ofFn fun i => BinaryRational.decode (c.get i)

theorem vertexPrices_value (c : BinaryFractionalRows.Row n) :
    decodeRow (vertexPrices c) = ConcurrentVertexCover.priceRow c := by
  apply Vector.ext
  intro i hi
  simp only [decodeRow,vertexPrices,FractionalCoverRawCore.get,ConcurrentVertexCover.priceRow,Vector.getElem_ofFn,
    rational]

theorem vertexPrices_fits (c : BinaryFractionalRows.Row n) {B : ℕ}
    (fit : ∀ i, BinaryRational.StoredBounded (c.get i) B) : RowBounded (vertexPrices c) B := by
  intro i
  simp only [vertexPrices,FractionalCoverRawCore.get_ofFn]
  exact BinaryFractionalRows.stored_raw_bound (fit i)

def edgeOracle (hn : 0 < n) (A : Adjacency n) (P : Vector (Edge n) m)
    (c : RawRow (n*n)) : MeasuredOracle (n*n) := fun y =>
  let calls := ConcurrentEdgeOracleWork.measuredPaths A P (decodeRow y)
  let col := ConcurrentEdgeOracle.column calls.1
  let pivot := choose (Nat.mul_pos hn hn) c col
  (⟨col,pivot.1⟩,calls.2+pivot.2)

theorem edgeOracle_value (hn : 0 < n) (A : Adjacency n) (P : Vector (Edge n) m) (c : RawRow (n*n)) :
    Refines (edgeOracle hn A P c) (ConcurrentEdgeOracle.oracle hn A P (decodeRow c)) := by
  intro y
  simp only [edgeOracle,ConcurrentEdgeOracle.oracle,ConcurrentEdgeOracleWork.paths_eq,
    MeasuredMultiplicityPivot.choose_value,MeasuredMultiplicityPivot.active,ConcurrentEdgeOracle.pivot,
    ConcurrentEdgeOracle.active]
  rfl

def vertexOracle (hn : 0 < n) (A : Adjacency n) (P : Vector (Edge n) m)
    (c : RawRow n) : MeasuredOracle n := fun y =>
  let calls := ConcurrentVertexOracleWork.paths A P (decodeRow y)
  let col := ConcurrentVertexOracle.column P calls.1
  let pivot := choose hn c col
  (⟨col,pivot.1⟩,calls.2+pivot.2)

theorem vertexOracle_value (hn : 0 < n) (A : Adjacency n) (P : Vector (Edge n) m) (c : RawRow n) :
    Refines (vertexOracle hn A P c) (ConcurrentVertexOracle.oracle hn A P (decodeRow c)) := by
  intro y
  simp only [vertexOracle,ConcurrentVertexOracle.oracle,ConcurrentVertexOracleWork.paths_value,
    MeasuredMultiplicityPivot.choose_value,MeasuredMultiplicityPivot.active,ConcurrentVertexOracle.pivot,
    ConcurrentVertexOracle.active]
  rfl

def edgeRun (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m) (k : ℕ) :
    Execution (n*n) :=
  let input := edgePrices A c
  run input (edgeOracle hn A P input) k

theorem edgeRun_value (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m) (k : ℕ) :
    let prices := ConcurrentEdgeCover.priceRow A c
    decoded (edgeRun hn A c P k).stored = MultiplicityCover.run prices (ConcurrentEdgeOracle.oracle hn A P prices) k := by
  simpa only [edgeRun,edgePrices_value] using
    MeasuredMultiplicityCover.run_value (edgePrices A c) _ _ (edgeOracle_value hn A P (edgePrices A c)) k

def vertexRun (hn : 0 < n) (A : Adjacency n) (c : BinaryFractionalRows.Row n)
    (P : Vector (Edge n) m) (k : ℕ) : Execution n :=
  let input := vertexPrices c
  run input (vertexOracle hn A P input) k

theorem vertexRun_value (hn : 0 < n) (A : Adjacency n) (c : BinaryFractionalRows.Row n)
    (P : Vector (Edge n) m) (k : ℕ) :
    let prices := ConcurrentVertexCover.priceRow c
    decoded (vertexRun hn A c P k).stored =
      MultiplicityCover.run prices (ConcurrentVertexOracle.oracle hn A P prices) k := by
  simpa only [vertexRun,vertexPrices_value] using
    MeasuredMultiplicityCover.run_value (vertexPrices c) _ _ (vertexOracle_value hn A P (vertexPrices c)) k

def oracleBound (r n m B k : ℕ) : ℕ :=
  (k+1)*(m*shortestBound n (weightWidth r B m k+1) 2 + work r B m)

theorem edgeRun_charge (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    {B : ℕ} (fit : MatrixFits c B) (k : ℕ) :
    (edgeRun hn A c P k).arithmetic ≤ startWork (n*n) B m+k*advanceWork (n*n) B m k ∧
      (edgeRun hn A c P k).oracleWork ≤ oracleBound (n*n) n m B k := by
  let input := edgePrices A c
  let oracle := edgeOracle hn A P input
  have prices := edgePrices_fits A c fit
  have counts (y : RawRow (n*n)) : ColumnFits (oracle y).1.column m := by
    change ColumnFits (edgeOracle hn A P input y).1.column m
    rw [edgeOracle_value hn A P input y]
    exact ConcurrentEdgeCoverWidths.oracle_columns hn A P _ _
  refine ⟨MeasuredMultiplicityCoverBounds.run_charge input oracle prices counts k,?_⟩
  apply MeasuredMultiplicityCoverBounds.run_oracle_charge input oracle prices counts _ (le_refl k)
  intro y shape
  have paths := ConcurrentEdgeOracleWork.charge_le A P (decodeRow y) (canonical_width y shape)
  have piv := MeasuredMultiplicityPivot.choose_charge (Nat.mul_pos hn hn) input _ prices (counts y)
  exact Nat.add_le_add paths piv

theorem vertexRun_charge (hn : 0 < n) (A : Adjacency n) (c : BinaryFractionalRows.Row n)
    (P : Vector (Edge n) m) {B : ℕ} (fit : ∀ i, BinaryRational.StoredBounded (c.get i) B) (k : ℕ) :
    (vertexRun hn A c P k).arithmetic ≤ startWork n B m+k*advanceWork n B m k ∧
      (vertexRun hn A c P k).oracleWork ≤ oracleBound n n m B k := by
  let input := vertexPrices c
  let oracle := vertexOracle hn A P input
  have prices := vertexPrices_fits c fit
  have counts (y : RawRow n) : ColumnFits (oracle y).1.column m :=
    ConcurrentVertexOracleWork.column_fits P (ConcurrentVertexOracleWork.paths A P (decodeRow y)).1
  refine ⟨MeasuredMultiplicityCoverBounds.run_charge input oracle prices counts k,?_⟩
  apply MeasuredMultiplicityCoverBounds.run_oracle_charge input oracle prices counts _ (le_refl k)
  intro y shape
  have paths := ConcurrentVertexOracleWork.paths_charge A P (decodeRow y) (canonical_width y shape)
  have piv := MeasuredMultiplicityPivot.choose_charge hn input _ prices (counts y)
  exact Nat.add_le_add paths piv

end DirectedFlowCutGap.MeasuredConcurrentCover
