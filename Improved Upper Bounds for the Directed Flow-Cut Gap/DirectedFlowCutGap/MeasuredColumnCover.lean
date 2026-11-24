import DirectedFlowCutGap.MeasuredPathColumn
import DirectedFlowCutGap.MeasuredCoverExtraWork
import DirectedFlowCutGap.MeasuredCanonicalCover

/-! Charge the binary path-to-column calculations inside the edge and vertex
cover. The new cover preserves even the raw stored state of its predecessor. -/
namespace DirectedFlowCutGap.MeasuredColumnCover

open BinaryFractionalWalkOracle (Adjacency)
open RationalEdgeThresholds (Weights)
open ConcurrentEdgeOracle (Edge)
open ConcurrentEdgeCoverWidths (MatrixFits)
open FractionalCoverRawCore (RawRow decodeRow)
open MeasuredCanonicalCover (readEdge readVertex arithmeticBound edgeOracleBound vertexOracleBound)
open MeasuredCanonicalPathInputs (edgePaths vertexPaths edgePaths_value vertexPaths_value)
open MeasuredMultiplicityCover (MeasuredOracle Execution run)
open MeasuredMultiplicityCoverBounds (Fields)
open MeasuredMultiplicityPivot (choose)

variable {n m : ℕ}

def edgeOracle (hn : 0 < n) (A : Adjacency n) (P : Vector (Edge n) m)
    (c : RawRow (n*n)) : MeasuredOracle (n*n) := fun y =>
  let calls := edgePaths A P y
  let column := MeasuredPathColumn.edge calls.1
  let pivot := choose (Nat.mul_pos hn hn) c column.1
  (⟨column.1,pivot.1⟩,calls.2+column.2+pivot.2)

theorem edgeOracle_value (hn : 0 < n) (A : Adjacency n) (P : Vector (Edge n) m)
    (c y : RawRow (n*n)) :
    (edgeOracle hn A P c y).1 = (MeasuredCanonicalCover.edgeOracle hn A P c y).1 := by
  simp only [edgeOracle,MeasuredCanonicalCover.edgeOracle,MeasuredPathColumn.edge_value]

theorem edgeOracle_charge (hn : 0 < n) (A : Adjacency n) (P : Vector (Edge n) m)
    (c y : RawRow (n*n)) :
    (edgeOracle hn A P c y).2 ≤ (MeasuredCanonicalCover.edgeOracle hn A P c y).2 +
      MeasuredPathColumn.edgeWork n m := by
  have fit : MeasuredPathColumn.PathsFit (edgePaths A P y).1 := by
    rw [edgePaths_value]
    exact MeasuredPathColumn.edge_cells_fit A P (decodeRow y)
  have count := MeasuredPathColumn.edge_charge _ fit
  simp only [edgeOracle,MeasuredCanonicalCover.edgeOracle,MeasuredPathColumn.edge_value]
  omega

def vertexOracle (hn : 0 < n) (A : Adjacency n) (P : Vector (Edge n) m)
    (c : RawRow n) : MeasuredOracle n := fun y =>
  let calls := vertexPaths A P y
  let column := MeasuredPathColumn.vertex P calls.1
  let pivot := choose hn c column.1
  (⟨column.1,pivot.1⟩,calls.2+column.2+pivot.2)

theorem vertexOracle_value (hn : 0 < n) (A : Adjacency n) (P : Vector (Edge n) m)
    (c y : RawRow n) :
    (vertexOracle hn A P c y).1 = (MeasuredCanonicalCover.vertexOracle hn A P c y).1 := by
  simp only [vertexOracle,MeasuredCanonicalCover.vertexOracle,MeasuredPathColumn.vertex_value]

theorem vertexOracle_charge (hn : 0 < n) (A : Adjacency n) (P : Vector (Edge n) m)
    (c y : RawRow n) :
    (vertexOracle hn A P c y).2 ≤ (MeasuredCanonicalCover.vertexOracle hn A P c y).2 +
      MeasuredPathColumn.vertexWork n m := by
  have fit : MeasuredPathColumn.PathsFit (vertexPaths A P y).1 := by
    rw [vertexPaths_value]
    exact MeasuredPathColumn.vertex_cells_fit A P (decodeRow y)
  have count := MeasuredPathColumn.vertex_charge P _ fit
  simp only [vertexOracle,MeasuredCanonicalCover.vertexOracle,MeasuredPathColumn.vertex_value]
  omega

def edgeRun (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (k : ℕ) : Execution (n*n) :=
  let input := readEdge A c
  let trace := run input.1 (edgeOracle hn A P input.1) k
  {trace with arithmetic := input.2+trace.arithmetic}

theorem edgeRun_preserves (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (k : ℕ) :
    (edgeRun hn A c P k).stored = (MeasuredCanonicalCover.edgeRun hn A c P k).stored ∧
    (edgeRun hn A c P k).arithmetic = (MeasuredCanonicalCover.edgeRun hn A c P k).arithmetic ∧
    (edgeRun hn A c P k).oracleWork ≤ (MeasuredCanonicalCover.edgeRun hn A c P k).oracleWork +
      (k+1)*MeasuredPathColumn.edgeWork n m := by
  obtain ⟨stored,paid,work⟩ := MeasuredCoverExtraWork.run_preserves (readEdge A c).1 _ _
    (edgeOracle_value hn A P _) (edgeOracle_charge hn A P _) k
  exact ⟨stored,congrArg ((readEdge A c).2+·) paid,work⟩

def vertexRun (hn : 0 < n) (A : Adjacency n) (c : BinaryFractionalRows.Row n)
    (P : Vector (Edge n) m) (k : ℕ) : Execution n :=
  let input := readVertex c
  let trace := run input.1 (vertexOracle hn A P input.1) k
  {trace with arithmetic := input.2+trace.arithmetic}

theorem vertexRun_preserves (hn : 0 < n) (A : Adjacency n) (c : BinaryFractionalRows.Row n)
    (P : Vector (Edge n) m) (k : ℕ) :
    (vertexRun hn A c P k).stored = (MeasuredCanonicalCover.vertexRun hn A c P k).stored ∧
    (vertexRun hn A c P k).arithmetic = (MeasuredCanonicalCover.vertexRun hn A c P k).arithmetic ∧
    (vertexRun hn A c P k).oracleWork ≤ (MeasuredCanonicalCover.vertexRun hn A c P k).oracleWork +
      (k+1)*MeasuredPathColumn.vertexWork n m := by
  obtain ⟨stored,paid,work⟩ := MeasuredCoverExtraWork.run_preserves (readVertex c).1 _ _
    (vertexOracle_value hn A P _) (vertexOracle_charge hn A P _) k
  exact ⟨stored,congrArg ((readVertex c).2+·) paid,work⟩

theorem edgeRun_bounds (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    {B : ℕ} (fit : MatrixFits c B) (k : ℕ) :
    Fields (edgeRun hn A c P k).stored B m k ∧
    (edgeRun hn A c P k).arithmetic ≤ arithmeticBound (n*n) m B k ∧
    (edgeRun hn A c P k).oracleWork ≤ edgeOracleBound n m B k+(k+1)*MeasuredPathColumn.edgeWork n m := by
  obtain ⟨stored,arithmetic,oracle⟩ := edgeRun_preserves hn A c P k
  obtain ⟨fields,before,paths⟩ := MeasuredCanonicalCover.edgeRun_bounds hn A c P fit k
  exact ⟨stored ▸ fields,arithmetic ▸ before,oracle.trans (Nat.add_le_add_right paths _)⟩

theorem vertexRun_bounds (hn : 0 < n) (A : Adjacency n) (c : BinaryFractionalRows.Row n)
    (P : Vector (Edge n) m) {B : ℕ} (fit : ∀ i, BinaryRational.StoredBounded (c.get i) B) (k : ℕ) :
    Fields (vertexRun hn A c P k).stored B m k ∧
    (vertexRun hn A c P k).arithmetic ≤ arithmeticBound n m B k ∧
    (vertexRun hn A c P k).oracleWork ≤ vertexOracleBound n m B k+(k+1)*MeasuredPathColumn.vertexWork n m := by
  obtain ⟨stored,arithmetic,oracle⟩ := vertexRun_preserves hn A c P k
  obtain ⟨fields,before,paths⟩ := MeasuredCanonicalCover.vertexRun_bounds hn A c P fit k
  exact ⟨stored ▸ fields,arithmetic ▸ before,oracle.trans (Nat.add_le_add_right paths _)⟩

end DirectedFlowCutGap.MeasuredColumnCover
