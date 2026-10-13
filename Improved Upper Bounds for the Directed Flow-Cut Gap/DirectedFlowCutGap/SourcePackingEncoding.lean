import DirectedFlowCutGap.SourcePackingCallLift

namespace DirectedFlowCutGap.SourcePacking
open BinaryArithmetic BinaryRational BinaryFractionalRows

def capacityFields {n : ℕ} (capacity : Row n) := IndexedRationalRead.fields capacity.toList
def matrixFields {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n) :=
  (GraphRelaxationRefinement.matrix adjacency).map (fun row => (row,([] : Bits)))
def demandFields {n : ℕ} (ds : List (BinaryFractionalWalkOracle.Pair n)) :=
  ds.map (fun d => (RowVertices.vertexLabel d.1,RowVertices.vertexLabel d.2))

def encode {n : ℕ} (capacity : Row n) (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (ds : List (BinaryFractionalWalkOracle.Pair n)) : Bits :=
  PackingSourceInput.encode (capacityFields capacity) (matrixFields adjacency) (demandFields ds)

def instructionBound {n : ℕ} (capacity : Row n) (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (ds : List (BinaryFractionalWalkOracle.Pair n)) : ℕ :=
  PackingSourceInput.instructions (capacityFields capacity) (matrixFields adjacency) (demandFields ds)+
    EnumeratedPacking.instructionBound ds.length n (SourceRowTableProgram.bits (capacityFields capacity))+2

theorem fields_width (rows : List Fraction) :
    ∀ x∈rows,StoredBounded x (SourceRowTableProgram.bits (IndexedRationalRead.fields rows)) := by
  induction rows with
  | nil => simp
  | cons x xs ih =>
    intro y hy
    rcases List.mem_cons.mp hy with rfl|hy
    · simp only [StoredBounded,IndexedRationalRead.fields,List.map_cons,SourceRowTableProgram.bits]
      constructor <;> omega
    · obtain ⟨h1,h2⟩ := ih y hy
      simp only [IndexedRationalRead.fields] at h1 h2
      simp only [StoredBounded,IndexedRationalRead.fields,List.map_cons,SourceRowTableProgram.bits]
      constructor <;> omega

end DirectedFlowCutGap.SourcePacking
