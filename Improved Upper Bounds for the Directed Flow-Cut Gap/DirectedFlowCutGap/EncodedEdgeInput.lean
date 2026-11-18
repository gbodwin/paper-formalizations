import DirectedFlowCutGap.EncodedSolverBits

/-!
# Reading rational edge costs from source tables

The matrix row count supplies the dimension. The first table contains
the square cost matrix in row-major order. The second and third tables
use the same adjacency and demand conventions as the vertex input.
-/

namespace DirectedFlowCutGap.EncodedEdgeInput

open BinaryArithmetic EncodedVertexInput

structure Input (n : ℕ) where
  adjacency : Vector (Vector Bool n) n
  demands : List (Fin n × Fin n)
  costs : Vector BinaryRational.Fraction (n * n)

def decodeInput {n : ℕ} (D : Input n) : EncodedEdgeLineInput.Input n :=
  let costs := BinaryFractionalRows.decodeRow D.costs
  ⟨D.adjacency, D.demands, Vector.ofFn fun s => Vector.ofFn fun t =>
    FractionalCoverRawCore.get costs (finProdFinEquiv (s, t))⟩

def encode {n : ℕ} (D : Input n) : Bits :=
  PackingSourceInput.encode (SourcePacking.capacityFields D.costs)
    (SourcePacking.matrixFields D.adjacency) (SourcePacking.demandFields D.demands)

private def assembleSized (n : ℕ) (capacity matrix demands : Table) : Option (Input n) := do
  let costs ← capacity.mapM readFraction
  let rows ← matrix.mapM (readMatrixRow n)
  let pairs ← demands.mapM (readDemand n)
  if h : costs.length = n * n ∧ rows.length = n then
    some ⟨⟨rows.toArray, by simpa using h.2⟩, pairs, ⟨costs.toArray, by simpa using h.1⟩⟩
  else none

def assemble (capacity matrix demands : Table) : Option (Σ n, Input n) :=
  (assembleSized matrix.length capacity matrix demands).map fun D => ⟨matrix.length, D⟩

def parse (source : Bits) : Option (Σ n, Input n) := do
  let (capacity, matrix, demands, suffix) ← readTables source
  if suffix.isEmpty then assemble capacity matrix demands else none

theorem parse_wire (capacity matrix demands : Table) :
    parse (PackingSourceInput.encode capacity matrix demands) = assemble capacity matrix demands := by
  have h := readTables_prefix capacity matrix demands []
  simp only [List.append_nil] at h
  simp [parse, h]

theorem assemble_fields {n : ℕ} (D : Input n) :
    assemble (SourcePacking.capacityFields D.costs) (SourcePacking.matrixFields D.adjacency)
      (SourcePacking.demandFields D.demands) = some ⟨n, D⟩ := by
  let matrix := SourcePacking.matrixFields D.adjacency
  let costs := SourcePacking.capacityFields D.costs
  let demands := SourcePacking.demandFields D.demands
  have hc : costs.mapM readFraction = some D.costs.toList := by
    exact mapM_encoded (fun (q : BinaryRational.Fraction) => (q.num, q.den))
      readFraction D.costs.toList readFraction_fields
  have hm : matrix.mapM (readMatrixRow n) = some D.adjacency.toList := by
    change ((D.adjacency.toList.map Vector.toList).map (fun row => (row, ([] : Bits)))).mapM _ = _
    rw [List.map_map]
    exact mapM_encoded (fun r => (r.toList, [])) (readMatrixRow n) _ readMatrixRow_fields
  have hd : demands.mapM (readDemand n) = some D.demands :=
    mapM_encoded (fun (d : Fin n × Fin n) => (RowVertices.vertexLabel d.1, RowVertices.vertexLabel d.2))
      (readDemand n) _ readDemand_fields
  have hn : matrix.length = n := by
    simpa [matrix, SourcePacking.matrixFields] using GraphRelaxationRefinement.matrix_length D.adjacency
  have hs : assembleSized n costs matrix demands = some D := by
    simp [assembleSized, hc, hm, hd]
    cases D
    rfl
  have transport (m : ℕ) (h : m = n) :
      (assembleSized m costs matrix demands).map (fun d => (⟨m, d⟩ : Σ k, Input k)) = some ⟨n, D⟩ := by
    subst m
    rw [hs]
    rfl
  exact transport _ hn

theorem parse_encode {n : ℕ} (D : Input n) : parse (encode D) = some ⟨n, D⟩ := by
  rw [encode, parse_wire, assemble_fields]

def bitTree (κ : ℕ) (mode : EncodedEdgeSolver.Mode) (source : Bits) :
    Option (Σ n, FiniteDrawTrees.Tree (EncodedEdgeSolver.Output n)) :=
  (parse source).map fun ⟨n, D⟩ => ⟨n, EncodedEdgeSolver.bitTree κ (decodeInput D) mode⟩

theorem bitTree_encode {n : ℕ} (κ : ℕ) (mode : EncodedEdgeSolver.Mode) (D : Input n) :
    bitTree κ mode (encode D) = some ⟨n, EncodedEdgeSolver.bitTree κ (decodeInput D) mode⟩ := by
  simp [bitTree, parse_encode]

end DirectedFlowCutGap.EncodedEdgeInput
