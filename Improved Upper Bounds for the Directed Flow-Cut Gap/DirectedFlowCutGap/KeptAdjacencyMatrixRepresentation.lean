import DirectedFlowCutGap.ActualKeptAdjacencyMatrix

namespace DirectedFlowCutGap.KeptAdjacencyMatrix
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead BinaryPointerListRead

theorem matrix_to_graph {heap : NaturalHeap} {p : ℕ} {rows : List Bits}
    (h : Matrix heap p rows) : GraphAdjacencyProgram.Matrix heap p rows := by
  induction h with
  | nil hp => exact ⟨[],rfl,.nil hp,by simp⟩
  | @cons p head tail u us hp hu _ ih =>
    obtain ⟨roots,hl,hr,hf⟩ := ih
    refine ⟨head::roots,by simpa using hl,.cons hp hr,?_⟩
    intro i hi
    cases i with
    | zero => exact hu
    | succ i => simpa using hf i (by simpa using hi)

theorem matrix_of_graph {heap : NaturalHeap} {p : ℕ} {rows : List Bits}
    (h : GraphAdjacencyProgram.Matrix heap p rows) : Matrix heap p rows := by
  obtain ⟨roots,hl,hp,hr⟩ := h
  induction hp generalizing rows with
  | nil hp =>
    cases rows with
    | nil => exact .nil hp
    | cons u us => simp at hl
  | @cons p head tail roots hp _ ih =>
    cases rows with
    | nil => simp at hl
    | cons u us =>
      apply GraphDiscoveryProgram.Vertices.cons hp (hr 0 (by simp))
      apply ih (by simpa using hl)
      intro i hi
      exact hr (Nat.succ i) (by simpa using hi)
end DirectedFlowCutGap.KeptAdjacencyMatrix

namespace DirectedFlowCutGap.KeptAdjacencyMatrix
open BinaryArithmetic

def keptFlags {n : ℕ} (mask : Vector Bool n) (s t : Fin n) : Bits :=
  List.ofFn fun u : Fin n => !mask[u.val] || decide (u=s) || decide (u=t)

theorem matrix_original {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (mask : Vector Bool n) (s t : Fin n) :
    matrix (keptFlags mask s t) (GraphRelaxationRefinement.matrix adjacency) (keptFlags mask s t)=
      GraphRelaxationRefinement.matrix (BinaryFractionalDispatch.keptAdjacency adjacency mask s t).1 := by
  rw [matrix_zip]
  apply List.ext_getElem
  · simp [keptFlags,GraphRelaxationRefinement.matrix]
  · intro i hi hj
    apply List.ext_getElem
    · simp [keptFlags,GraphRelaxationRefinement.matrix]
    · intro j hji hjj
      simp [keptFlags,GraphRelaxationRefinement.matrix,BinaryFractionalDispatch.keptAdjacency,
        EncodedRoundingInput.tabulate_value, BinaryFractionalWalkOracle.adjacent,EncodedArrayStorage.readCallback]
end DirectedFlowCutGap.KeptAdjacencyMatrix
