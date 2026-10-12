import DirectedFlowCutGap.PackingStartGraphCalls

namespace DirectedFlowCutGap.PackingStart
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

def Input {n : ℕ} (heap : NaturalHeap) (root : ℕ) (label : Fin n → Bits)
    (adjacency : BinaryFractionalWalkOracle.Adjacency n) (capacity : Row n)
    (xs : List DemandCollection.Demand) : Prop :=
  ∃ demands metadata,heap[root]?=some (.pair demands metadata) ∧
    DemandCollection.DemandList heap demands xs ∧
    PackingGraphContext.Static heap metadata label adjacency capacity

def WeightFrame (heap : NaturalHeap) (root capacity input weights : ℕ) : Prop :=
  ∃ frame,heap[root]?=some (.pair weights frame) ∧ heap[frame]?=some (.pair capacity input)

theorem static_extend {n : ℕ} {heap : NaturalHeap} {root : ℕ} {label : Fin n → Bits}
    {adjacency : BinaryFractionalWalkOracle.Adjacency n} {capacity : Row n}
    (h : PackingGraphContext.Static heap root label adjacency capacity) (ext : NaturalHeap) :
    PackingGraphContext.Static (heap++ext) root label adjacency capacity := by
  obtain ⟨vertices,metadata,matrix,post,hroot,hmeta,hv,hm,hp⟩ := h
  exact ⟨vertices,metadata,matrix,post,lookup_extend hroot ext,lookup_extend hmeta ext,
    GraphDiscoveryProgram.vertices_extend hv ext,GraphAdjacencyProgram.matrix_extend hm ext,
    OracleChoice.graph_context_extend hp ext⟩

theorem input_extend {n : ℕ} {heap : NaturalHeap} {root : ℕ} {label : Fin n → Bits}
    {adjacency : BinaryFractionalWalkOracle.Adjacency n} {capacity : Row n}
    {xs : List DemandCollection.Demand} (h : Input heap root label adjacency capacity xs) (ext : NaturalHeap) :
    Input (heap++ext) root label adjacency capacity xs := by
  obtain ⟨d,m,hp,hd,hm⟩ := h
  exact ⟨d,m,lookup_extend hp ext,DemandCollection.demands_extend hd ext,static_extend hm ext⟩

theorem weight_frame_extend {heap : NaturalHeap} {root capacity input weights : ℕ}
    (h : WeightFrame heap root capacity input weights) (ext : NaturalHeap) :
    WeightFrame (heap++ext) root capacity input weights := by
  obtain ⟨r,hp,hq⟩ := h
  exact ⟨r,lookup_extend hp ext,lookup_extend hq ext⟩
end DirectedFlowCutGap.PackingStart
