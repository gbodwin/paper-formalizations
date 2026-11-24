import DirectedFlowCutGap.MeasuredCanonicalPathInputs

/-! The measured graph cover includes the canonical normalization it uses
before its binary searches. Its decoded trace is unchanged. -/
namespace DirectedFlowCutGap.MeasuredCanonicalCover

open BinaryFractionalWalkOracle (Adjacency decodeCost)
open ConcurrentEdgeOracle (Edge edge)
open FractionalCoverRawCore (RawRow RowBounded decodeRow)
open MeasuredConcurrentCover (edgePrices edgePrices_fits vertexPrices vertexPrices_fits)
open MeasuredMultiplicityCover (MeasuredOracle Execution run decoded Refines)
open MeasuredMultiplicityCoverBounds (Fields run_fields run_charge run_oracle_charge startWork advanceWork)
open MeasuredMultiplicityPivot (choose choose_value choose_charge work)
open MeasuredCanonicalPathInputs (edgePaths vertexPaths edgePaths_charge vertexPaths_charge)
open MultiplicityCoverWidths (ColumnFits weightWidth)
open RationalEdgeThresholds (Weights cost)
open ConcurrentEdgeCoverWidths (MatrixFits)
open RawNonnegativeRational (Code)

variable {n m : ℕ}

def edgeOracle (hn : 0 < n) (A : Adjacency n) (P : Vector (Edge n) m)
    (c : RawRow (n*n)) : MeasuredOracle (n*n) := fun y =>
  let paths := edgePaths A P y
  let column := ConcurrentEdgeOracle.column paths.1
  let pivot := choose (Nat.mul_pos hn hn) c column
  (⟨column,pivot.1⟩,paths.2+pivot.2)

theorem edgeOracle_value (hn : 0 < n) (A : Adjacency n) (P : Vector (Edge n) m) (c : RawRow (n*n)) :
    Refines (edgeOracle hn A P c) (ConcurrentEdgeOracle.oracle hn A P (decodeRow c)) := by
  intro y
  simp only [edgeOracle,ConcurrentEdgeOracle.oracle,MeasuredCanonicalPathInputs.edgePaths_value,choose_value,
    MeasuredMultiplicityPivot.active,ConcurrentEdgeOracle.pivot,ConcurrentEdgeOracle.active]
  rfl

def vertexOracle (hn : 0 < n) (A : Adjacency n) (P : Vector (Edge n) m)
    (c : RawRow n) : MeasuredOracle n := fun y =>
  let paths := vertexPaths A P y
  let column := ConcurrentVertexOracle.column P paths.1
  let pivot := choose hn c column
  (⟨column,pivot.1⟩,paths.2+pivot.2)

theorem vertexOracle_value (hn : 0 < n) (A : Adjacency n) (P : Vector (Edge n) m) (c : RawRow n) :
    Refines (vertexOracle hn A P c) (ConcurrentVertexOracle.oracle hn A P (decodeRow c)) := by
  intro y
  simp only [vertexOracle,ConcurrentVertexOracle.oracle,MeasuredCanonicalPathInputs.vertexPaths_value,choose_value,
    MeasuredMultiplicityPivot.active,ConcurrentVertexOracle.pivot,ConcurrentVertexOracle.active]
  rfl

def readEdge (A : Adjacency n) (c : Weights n) : RawRow (n*n) × ℕ :=
  MeasuredBudgetPrices.tabulate fun i =>
    let uv := edge i
    if A[uv.1.val][uv.2.val] then BinaryRawRational.decode ((cost c) uv).1 else (Code.one,0)

theorem readEdge_value (A : Adjacency n) (c : Weights n) : (readEdge A c).1 = edgePrices A c := by
  apply Vector.ext
  intro i hi
  simp only [readEdge,MeasuredBudgetPrices.tabulate_value,edgePrices,Vector.getElem_ofFn]
  split
  · exact BinaryRawRational.decode_value _
  · rfl

theorem readEdge_charge (A : Adjacency n) (c : Weights n) {B : ℕ} (fit : MatrixFits c B) :
    (readEdge A c).2 ≤ (n*n)*(40*(B+1)^2) := by
  apply MeasuredBudgetPrices.tabulate_charge
  intro i
  dsimp only
  split
  · exact BinaryRawRational.decode_paid (fit (edge i).1 (edge i).2)
  · exact Nat.zero_le _

def readVertex (c : BinaryFractionalRows.Row n) : RawRow n × ℕ :=
  MeasuredBudgetPrices.tabulate fun i => BinaryRawRational.decode (c.get i)

theorem readVertex_value (c : BinaryFractionalRows.Row n) : (readVertex c).1 = vertexPrices c := by
  apply Vector.ext
  intro i hi
  simp only [readVertex,MeasuredBudgetPrices.tabulate_value,vertexPrices,Vector.getElem_ofFn,
    BinaryRawRational.decode_value]

theorem readVertex_charge (c : BinaryFractionalRows.Row n) {B : ℕ}
    (fit : ∀ i, BinaryRational.StoredBounded (c.get i) B) : (readVertex c).2 ≤ n*(40*(B+1)^2) :=
  MeasuredBudgetPrices.tabulate_charge _ (fun i => BinaryRawRational.decode_paid (fit i))

def edgeRun (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m) (k : ℕ) :
    Execution (n*n) :=
  let input := readEdge A c
  let trace := run input.1 (edgeOracle hn A P input.1) k
  {trace with arithmetic := input.2+trace.arithmetic}

theorem edgeRun_value (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m) (k : ℕ) :
    let prices := ConcurrentEdgeCover.priceRow A c
    decoded (edgeRun hn A c P k).stored = MultiplicityCover.run prices (ConcurrentEdgeOracle.oracle hn A P prices) k := by
  simpa only [edgeRun,readEdge_value,MeasuredConcurrentCover.edgePrices_value] using
    MeasuredMultiplicityCover.run_value (edgePrices A c) _ _ (edgeOracle_value hn A P (edgePrices A c)) k

def vertexRun (hn : 0 < n) (A : Adjacency n) (c : BinaryFractionalRows.Row n)
    (P : Vector (Edge n) m) (k : ℕ) : Execution n :=
  let input := readVertex c
  let trace := run input.1 (vertexOracle hn A P input.1) k
  {trace with arithmetic := input.2+trace.arithmetic}

theorem vertexRun_value (hn : 0 < n) (A : Adjacency n) (c : BinaryFractionalRows.Row n)
    (P : Vector (Edge n) m) (k : ℕ) :
    let prices := ConcurrentVertexCover.priceRow c
    decoded (vertexRun hn A c P k).stored =
      MultiplicityCover.run prices (ConcurrentVertexOracle.oracle hn A P prices) k := by
  simpa only [vertexRun,readVertex_value,MeasuredConcurrentCover.vertexPrices_value] using
    MeasuredMultiplicityCover.run_value (vertexPrices c) _ _ (vertexOracle_value hn A P (vertexPrices c)) k

def edgeOracleBound (n m B k : ℕ) : ℕ :=
  (k+1)*(MeasuredCanonicalPathInputs.edgeWork n m (weightWidth (n*n) B m k)+work (n*n) B m)

def vertexOracleBound (n m B k : ℕ) : ℕ :=
  (k+1)*(MeasuredCanonicalPathInputs.vertexWork n m (weightWidth n B m k)+work n B m)

def arithmeticBound (r m B k : ℕ) : ℕ := r*(40*(B+1)^2)+startWork r B m+k*advanceWork r B m k

theorem edgeRun_bounds (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    {B : ℕ} (fit : MatrixFits c B) (k : ℕ) :
    Fields (edgeRun hn A c P k).stored B m k ∧
    (edgeRun hn A c P k).arithmetic ≤ arithmeticBound (n*n) m B k ∧
      (edgeRun hn A c P k).oracleWork ≤ edgeOracleBound n m B k := by
  let input := edgePrices A c
  let oracle := edgeOracle hn A P input
  have prices := edgePrices_fits A c fit
  have counts (y : RawRow (n*n)) : ColumnFits (oracle y).1.column m := by
    change ColumnFits (edgeOracle hn A P input y).1.column m
    rw [edgeOracle_value hn A P input y]
    exact ConcurrentEdgeCoverWidths.oracle_columns hn A P _ _
  simp only [edgeRun,readEdge_value]
  refine ⟨run_fields input oracle prices counts k,?_,?_⟩
  · simpa only [arithmeticBound,Nat.add_assoc] using
      Nat.add_le_add (readEdge_charge A c fit) (run_charge input oracle prices counts k)
  · apply run_oracle_charge input oracle prices counts _ (le_refl k)
    intro y shape
    exact Nat.add_le_add (edgePaths_charge A P y shape)
      (choose_charge (Nat.mul_pos hn hn) input _ prices (counts y))

theorem vertexRun_bounds (hn : 0 < n) (A : Adjacency n) (c : BinaryFractionalRows.Row n)
    (P : Vector (Edge n) m) {B : ℕ} (fit : ∀ i, BinaryRational.StoredBounded (c.get i) B) (k : ℕ) :
    Fields (vertexRun hn A c P k).stored B m k ∧
    (vertexRun hn A c P k).arithmetic ≤ arithmeticBound n m B k ∧
      (vertexRun hn A c P k).oracleWork ≤ vertexOracleBound n m B k := by
  let input := vertexPrices c
  let oracle := vertexOracle hn A P input
  have prices := vertexPrices_fits c fit
  have counts (y : RawRow n) : ColumnFits (oracle y).1.column m :=
    ConcurrentVertexOracleWork.column_fits P (vertexPaths A P y).1
  simp only [vertexRun,readVertex_value]
  refine ⟨run_fields input oracle prices counts k,?_,?_⟩
  · simpa only [arithmeticBound,Nat.add_assoc] using
      Nat.add_le_add (readVertex_charge c fit) (run_charge input oracle prices counts k)
  · apply run_oracle_charge input oracle prices counts _ (le_refl k)
    intro y shape
    exact Nat.add_le_add (vertexPaths_charge A P y shape) (choose_charge hn input _ prices (counts y))

end DirectedFlowCutGap.MeasuredCanonicalCover
