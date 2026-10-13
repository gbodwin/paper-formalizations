import DirectedFlowCutGap.AvoidingKeptPathCalls

namespace DirectedFlowCutGap.AvoidingKeptPath
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor
open IntegralNetworkFlow IntegralNetworkFlow.Tabulated

def kept (s t : Bits) (vs : List Bits) (costs : List (Bits × Bits)) (rows : List Bits) : List Bits :=
  KeptAdjacencyInput.result s t vs costs rows

def result (s t : Bits) (vs : List Bits) (costs : List (Bits × Bits)) (rows : List Bits) : Option GraphWalkExtension.Walk :=
  AvoidingShortest.result vs (kept s t vs costs rows) s t

def steps (s t : Bits) (vs : List Bits) (costs : List (Bits × Bits)) (rows : List Bits) : ℕ :=
  KeptAdjacencyInput.steps s t vs costs rows+AvoidingShortest.steps vs (kept s t vs costs rows) s t+12

def cells (s t : Bits) (vs : List Bits) (costs : List (Bits × Bits)) (rows : List Bits) : ℕ :=
  KeptAdjacencyInput.cells s t vs costs rows+AvoidingShortest.cells vs (kept s t vs costs rows) s t+2

theorem search_return {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n) (s t : Fin n)
    (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    {heap : NaturalHeap} {a b : ℕ}
    (input : GraphDiscoveryProgram.Vertices heap a (List.ofFn label))
    (metadata : KeptAdjacencyInput.Context heap b (label s) (label t)
      (IndexedRationalRead.fields costs.toList) (GraphRelaxationRefinement.matrix adjacency))
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 1800)
    (stack : List (Frame ℕ 1800)) (source : Bits) :
    ∃ ext root,ext.length=cells (label s) (label t) (List.ofFn label)
      (IndexedRationalRead.fields costs.toList) (GraphRelaxationRefinement.matrix adjacency) ∧
      NaturalRun program (steps (label s) (label t) (List.ofFn label)
        (IndexedRationalRead.fields costs.toList) (GraphRelaxationRefinement.matrix adjacency))
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 1770) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      GraphDiscoveryProgram.StoredOption (heap++ext) root
        (result (label s) (label t) (List.ofFn label) (IndexedRationalRead.fields costs.toList)
          (GraphRelaxationRefinement.matrix adjacency)) := by
  obtain ⟨mc,ar,hb,hm,ha⟩ := metadata
  obtain ⟨ep,sr,tr,cr,hmc,he,hs,ht,hcost⟩ := hm
  let frames : List (Frame ℕ 1800) := ⟨pc,.r3,saved⟩::stack
  let scratch : Cell ℕ := .pair a b
  let h0 : NaturalHeap := heap++[scratch]
  have hi0 := GraphDiscoveryProgram.vertices_extend input [scratch]
  have hm0 := KeptAdjacencyInput.context_extend
    (show KeptAdjacencyInput.Context heap b (label s) (label t)
      (IndexedRationalRead.fields costs.toList) (GraphRelaxationRefinement.matrix adjacency) from
        ⟨mc,ar,hb,⟨ep,sr,tr,cr,hmc,he,hs,ht,hcost⟩,ha⟩) [scratch]
  have aligned : (List.ofFn label).length=(IndexedRationalRead.fields costs.toList).length := by
    simp [IndexedRationalRead.fields]
  have height : (GraphRelaxationRefinement.matrix adjacency).length=(List.ofFn label).length := by
    simp [GraphRelaxationRefinement.matrix_length]
  have widths : ∀ u∈GraphRelaxationRefinement.matrix adjacency,u.length=(List.ofFn label).length := by
    intro u hu
    unfold GraphRelaxationRefinement.matrix at hu
    obtain ⟨row,_,rfl⟩ := List.mem_map.mp hu
    simp
  obtain ⟨e1,mroot,l1,mrun,mrep⟩ := matrix_return hi0 hm0 aligned height widths
    (next+1) next d (by simp [hn]) ⟨a,b,next,d⟩ 1772 frames source
  let h1 := h0++e1
  let n1 := next+1+e1.length
  let static : Cell ℕ := .pair mroot ep
  let h2 := h1++[static]
  have hn1 : n1=h1.length := by simp [n1,h1,h0,hn];omega
  have hp : h2[n1]?=some static := by simp [h2,hn1]
  let keptGraph := (BinaryFractionalDispatch.keptAdjacency adjacency (BinaryFractionalDispatch.zeroMask costs).1 s t).1
  have mk : kept (label s) (label t) (List.ofFn label) (IndexedRationalRead.fields costs.toList)
      (GraphRelaxationRefinement.matrix adjacency)=GraphRelaxationRefinement.matrix keptGraph :=
    KeptAdjacencyInput.result_original label hlabel s t costs adjacency
  have mg : GraphAdjacencyProgram.Matrix h2 mroot (GraphRelaxationRefinement.matrix keptGraph) := by
    rw [←mk]
    exact KeptAdjacencyMatrix.matrix_to_graph (GraphDiscoveryProgram.vertices_extend mrep _)
  have he2 : h2[ep]?=some (.pair sr tr) := lookup_extend (lookup_extend (lookup_extend he _) _) _
  have hs2 := boolList_extend (boolList_extend (boolList_extend hs [scratch]) e1) [static]
  have ht2 := boolList_extend (boolList_extend (boolList_extend ht [scratch]) e1) [static]
  have metadata2 : AvoidingZeroContext.Static h2 n1 (GraphRelaxationRefinement.matrix keptGraph) (label s) (label t) :=
    ⟨mroot,ep,sr,tr,hp,he2,mg,hs2,ht2⟩
  obtain ⟨e2,root,l2,srun,srep⟩ := shortest_return keptGraph s t label hlabel
    (GraphDiscoveryProgram.vertices_extend (GraphDiscoveryProgram.vertices_extend hi0 e1) [static]) metadata2
    (n1+1) next mroot (by change n1+1=h2.length; simp only [h2,List.length_append,List.length_singleton,hn1]) ⟨a,n1,next,mroot⟩ 1777 frames source
  have t0 : tickNatural program (state heap next a b c d frames source 1770)=
      some ⟨state h0 (next+1) a b next d frames source 1771,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,h0,scratch]
  have t1 : tickNatural program (state h0 (next+1) a b next d frames source 1771)=
      some ⟨state h0 (next+1) a b next d (⟨1772,.r3,⟨a,b,next,d⟩⟩::frames) source 318,[],0⟩ := rfl
  have hb1 : h1[b]?=some (.pair mc ar) := lookup_extend (lookup_extend hb _) _
  have hmc1 : h1[mc]?=some (.pair ep cr) := lookup_extend (lookup_extend hmc _) _
  have t2 : tickNatural program (state h1 n1 a b next mroot frames source 1772)=
      some ⟨state h1 n1 a mc next mroot frames source 1773,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hb1]
  have t3 : tickNatural program (state h1 n1 a mc next mroot frames source 1773)=
      some ⟨state h1 n1 a ep next mroot frames source 1774,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hmc1]
  have t4 : tickNatural program (state h1 n1 a ep next mroot frames source 1774)=
      some ⟨state h2 (n1+1) a n1 next mroot frames source 1775,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,h2,static]
  have hscratch : h2[next]?=some scratch := lookup_extend (lookup_extend (by simp [h0,hn]) e1) [static]
  have t5 : tickNatural program (state h2 (n1+1) a n1 next mroot frames source 1775)=
      some ⟨state h2 (n1+1) a n1 next mroot frames source 1776,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hscratch,scratch]
  have t6 : tickNatural program (state h2 (n1+1) a n1 next mroot frames source 1776)=
      some ⟨state h2 (n1+1) a n1 next mroot (⟨1777,.r3,⟨a,n1,next,mroot⟩⟩::frames) source 1758,[],0⟩ := rfl
  have t7 : tickNatural program (state (h2++e2) (n1+1+e2.length) a n1 next root frames source 1777)=
      some ⟨state (h2++e2) (n1+1+e2.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,frames]
  have last := run_append srun (.step t7 (.done _))
  have middle := NaturalRun.step t2 (.step t3 (.step t4 (.step t5 (.step t6 last))))
  have whole := NaturalRun.step t0 (.step t1 (run_append mrun middle))
  refine ⟨[scratch]++e1++[static]++e2,root,?_,?_,?_⟩
  · simp [cells,mk,l1,l2];omega
  · convert whole using 1 <;> simp [steps,mk,state,h2,h1,h0,n1,List.append_assoc,Nat.add_assoc] <;> omega
  · simpa only [result,mk,h2,h1,h0,List.append_assoc] using srep
end DirectedFlowCutGap.AvoidingKeptPath
