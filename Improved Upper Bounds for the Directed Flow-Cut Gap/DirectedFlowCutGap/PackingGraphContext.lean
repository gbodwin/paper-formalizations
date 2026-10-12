import DirectedFlowCutGap.ActualGraphOracle
import DirectedFlowCutGap.CanonicalRationalSum

/-! A fresh weight row is installed in a real oracle context. The static
metadata contains only the original enumeration, adjacency and capacity data. -/
namespace DirectedFlowCutGap.PackingGraphContext
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram IntegralNetworkFlow IntegralNetworkFlow.Tabulated
open CanonicalRationalSum (StoredList list_extend)

def Static {n : ℕ} (heap : NaturalHeap) (root : ℕ) (label : Fin n → Bits)
    (adjacency : BinaryFractionalWalkOracle.Adjacency n) (capacity : Row n) : Prop :=
  ∃ vertices metadata matrix post,heap[root]?=some (.pair vertices metadata) ∧
    heap[metadata]?=some (.pair matrix post) ∧
    GraphDiscoveryProgram.Vertices heap vertices ((ResidualSearch.Enumeration.fin n).vertices.map label) ∧
    GraphAdjacencyProgram.Matrix heap matrix (GraphRelaxationRefinement.matrix adjacency) ∧
    CapacityBottleneck.GraphContext heap post label capacity

def program : Program 10 := fun pc => match pc.val with
  | 0 => .field .r2 .r1 false 1
  | 1 => .field .r1 .r1 true 2
  | 2 => .field .r3 .r1 false 3
  | 3 => .make .r0 (.pair .r3 .r0) 4
  | 4 => .make .r0 (.pair .r2 .r0) 5
  | 5 => .field .r1 .r1 true 6
  | 6 => .make .r3 (.pair .r0 .r1) 7
  | 7 => .ret .r3
  | 8 => .call 0 9 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 10)) (source : Bits) (pc : Fin 10) : NaturalState 10 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

theorem row_table {heap : NaturalHeap} {root : ℕ} {xs : List Fraction}
    (h : StoredList heap root xs) : WordPairTableRead.Table heap root (IndexedRationalRead.fields xs) := by
  induction h with
  | nil hp => exact .nil hp
  | cons hp hq _ ih =>
    obtain ⟨num,den,hpair,hn,hd⟩ := hq
    exact .cons hp hpair hn hd ih

theorem construct_return {n : ℕ} (label : Fin n → Bits)
    (adjacency : BinaryFractionalWalkOracle.Adjacency n) (capacity y : Row n)
    {heap : NaturalHeap} {a b : ℕ} (weights : StoredList heap a y.toList)
    (metadata : Static heap b label adjacency capacity) (next c d : ℕ)
    (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 10)
    (stack : List (Frame ℕ 10)) (source : Bits) :
    ∃ ext root,ext.length=3 ∧ NaturalRun program 8
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 0) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      GraphOracleMachine.Context (heap++ext) root label adjacency capacity y := by
  obtain ⟨vertices,detailRoot,matrix,post,hb,hm,hv,ha,hp⟩ := metadata
  let frames : List (Frame ℕ 10) := ⟨pc,.r3,saved⟩::stack
  let h1 := heap++[.pair matrix a]
  let h2 := h1++[.pair vertices next]
  let h3 := h2++[.pair (next+1) post]
  have t0 : tickNatural program (state heap next a b c d frames source 0)=
      some ⟨state heap next a b vertices d frames source 1,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hb]
  have t1 : tickNatural program (state heap next a b vertices d frames source 1)=
      some ⟨state heap next a detailRoot vertices d frames source 2,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hb]
  have t2 : tickNatural program (state heap next a detailRoot vertices d frames source 2)=
      some ⟨state heap next a detailRoot vertices matrix frames source 3,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hm]
  have t3 : tickNatural program (state heap next a detailRoot vertices matrix frames source 3)=
      some ⟨state h1 (next+1) next detailRoot vertices matrix frames source 4,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,h1]
  have t4 : tickNatural program (state h1 (next+1) next detailRoot vertices matrix frames source 4)=
      some ⟨state h2 (next+2) (next+1) detailRoot vertices matrix frames source 5,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,h2,Nat.add_assoc]
  have hm2 : h2[detailRoot]?=some (.pair matrix post) := lookup_extend (lookup_extend hm _) _
  have t5 : tickNatural program (state h2 (next+2) (next+1) detailRoot vertices matrix frames source 5)=
      some ⟨state h2 (next+2) (next+1) post vertices matrix frames source 6,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hm2]
  have t6 : tickNatural program (state h2 (next+2) (next+1) post vertices matrix frames source 6)=
      some ⟨state h3 (next+3) (next+1) post vertices (next+2) frames source 7,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,h3,Nat.add_assoc]
  have t7 : tickNatural program (state h3 (next+3) (next+1) post vertices (next+2) frames source 7)=
      some ⟨state h3 (next+3) saved.a saved.b saved.c (next+2) stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,frames]
  let ext : NaturalHeap := [.pair matrix a,.pair vertices next,.pair (next+1) post]
  have eh : heap++ext=h3 := by simp [ext,h3,h2,h1,List.append_assoc]
  refine ⟨ext,next+2,rfl,?_,?_⟩
  · simpa [ext,eh] using NaturalRun.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.done _))))))))
  · refine ⟨next+1,post,?_,?_,OracleChoice.graph_context_extend hp ext⟩
    · simp [ext,hn]
    · refine ⟨vertices,next,matrix,a,?_,?_,GraphDiscoveryProgram.vertices_extend hv ext,
        GraphAdjacencyProgram.matrix_extend ha ext,row_table (list_extend weights ext)⟩
      · simp [ext,hn]
      · simp [ext,hn]
end DirectedFlowCutGap.PackingGraphContext
