import DirectedFlowCutGap.AvoidingDemandScanCall

namespace DirectedFlowCutGap.AvoidingDemandScan
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor
open IntegralNetworkFlow IntegralNetworkFlow.Tabulated

theorem head_query {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n) (s t : Fin n)
    (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    {heap : NaturalHeap} {a b item tail : ℕ}
    (head : heap[a]?=some (.pair item tail))
    (demand : EmptyDemandEdge.Demand heap item (label s) (label t))
    (context : Context heap b (List.ofFn label) (IndexedRationalRead.fields costs.toList)
      (GraphRelaxationRefinement.matrix adjacency))
    (next c d : ℕ) (hn : next=heap.length) (stack : List (Frame ℕ 1900)) (source : Bits) :
    ∃ ext root vr,ext.length=AvoidingKeptPath.cells (label s) (label t) (List.ofFn label)
      (IndexedRationalRead.fields costs.toList) (GraphRelaxationRefinement.matrix adjacency)+3 ∧
      NaturalRun program (AvoidingKeptPath.steps (label s) (label t) (List.ofFn label)
        (IndexedRationalRead.fields costs.toList) (GraphRelaxationRefinement.matrix adjacency)+13)
        (state heap next a b c d stack source 1813) []
        (state (heap++ext) (next+ext.length) vr (next+2) next root stack source 1824) ∧
      GraphDiscoveryProgram.StoredOption (heap++ext) root
        (AvoidingKeptPath.result (label s) (label t) (List.ofFn label)
          (IndexedRationalRead.fields costs.toList) (GraphRelaxationRefinement.matrix adjacency)) ∧
      (heap++ext)[next]?=some (.pair a b) := by
  obtain ⟨vr,detail,cr,ar,hb,hd,hv,hc,ha⟩ := context
  obtain ⟨sr,tr,hi,hs,ht⟩ := demand
  let scratch : Cell ℕ := .pair a b
  let h0 := heap++[scratch]
  let maskctx : Cell ℕ := .pair item cr
  let h1 := h0++[maskctx]
  let queryctx : Cell ℕ := .pair (next+1) ar
  let h2 := h1++[queryctx]
  have sc0 : h0[next]?=some scratch := by simp [h0,hn]
  have mc1 : h1[next+1]?=some maskctx := by simp [h1,h0,hn]
  have qc2 : h2[next+2]?=some queryctx := by simp [h2,h1,h0,hn]
  have hu2 := GraphDiscoveryProgram.vertices_extend (GraphDiscoveryProgram.vertices_extend
    (GraphDiscoveryProgram.vertices_extend hv [scratch]) [maskctx]) [queryctx]
  have hc2 := BinaryIndexedPairRead.table_extend (BinaryIndexedPairRead.table_extend
    (BinaryIndexedPairRead.table_extend hc [scratch]) [maskctx]) [queryctx]
  have ha2 := GraphDiscoveryProgram.vertices_extend (GraphDiscoveryProgram.vertices_extend
    (GraphDiscoveryProgram.vertices_extend ha [scratch]) [maskctx]) [queryctx]
  have hi2 := lookup_extend (lookup_extend (lookup_extend hi [scratch]) [maskctx]) [queryctx]
  have hs2 := boolList_extend (boolList_extend (boolList_extend hs [scratch]) [maskctx]) [queryctx]
  have ht2 := boolList_extend (boolList_extend (boolList_extend ht [scratch]) [maskctx]) [queryctx]
  have metadata : KeptAdjacencyInput.Context h2 (next+2) (label s) (label t)
      (IndexedRationalRead.fields costs.toList) (GraphRelaxationRefinement.matrix adjacency) :=
    ⟨next+1,ar,qc2,⟨item,sr,tr,cr,lookup_extend mc1 _,hi2,hs2,ht2,hc2⟩,ha2⟩
  obtain ⟨e,root,len,run,rep⟩ := query_return adjacency costs s t label hlabel hu2 metadata
    (next+3) next ar (by simp [hn]) ⟨vr,next+2,next,ar⟩ 1824 stack source
  have head0 : h0[a]?=some (.pair item tail) := lookup_extend head _
  have hb0 : h0[b]?=some (.pair vr detail) := lookup_extend hb _
  have hd0 : h0[detail]?=some (.pair cr ar) := lookup_extend hd _
  have hb1 : h1[b]?=some (.pair vr detail) := lookup_extend hb0 _
  have hd1 : h1[detail]?=some (.pair cr ar) := lookup_extend hd0 _
  have sc2 : h2[next]?=some scratch := lookup_extend (lookup_extend sc0 _) _
  have hb2 : h2[b]?=some (.pair vr detail) := lookup_extend hb1 _
  have t0 : tickNatural program (state heap next a b c d stack source 1813)=
      some ⟨state h0 (next+1) a b next d stack source 1814,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,h0,scratch]
  have t1 : tickNatural program (state h0 (next+1) a b next d stack source 1814)=
      some ⟨state h0 (next+1) item b next d stack source 1815,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,head0]
  have t2 : tickNatural program (state h0 (next+1) item b next d stack source 1815)=
      some ⟨state h0 (next+1) item b next detail stack source 1816,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hb0]
  have t3 : tickNatural program (state h0 (next+1) item b next detail stack source 1816)=
      some ⟨state h0 (next+1) item b next cr stack source 1817,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hd0]
  have t4 : tickNatural program (state h0 (next+1) item b next cr stack source 1817)=
      some ⟨state h1 (next+2) (next+1) b next cr stack source 1818,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,h1,maskctx,Nat.add_assoc]
  have t5 : tickNatural program (state h1 (next+2) (next+1) b next cr stack source 1818)=
      some ⟨state h1 (next+2) (next+1) b next detail stack source 1819,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hb1]
  have t6 : tickNatural program (state h1 (next+2) (next+1) b next detail stack source 1819)=
      some ⟨state h1 (next+2) (next+1) b next ar stack source 1820,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hd1]
  have t7 : tickNatural program (state h1 (next+2) (next+1) b next ar stack source 1820)=
      some ⟨state h2 (next+3) (next+1) (next+2) next ar stack source 1821,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,h2,queryctx,Nat.add_assoc]
  have t8 : tickNatural program (state h2 (next+3) (next+1) (next+2) next ar stack source 1821)=
      some ⟨state h2 (next+3) b (next+2) next ar stack source 1822,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,sc2,scratch]
  have t9 : tickNatural program (state h2 (next+3) b (next+2) next ar stack source 1822)=
      some ⟨state h2 (next+3) vr (next+2) next ar stack source 1823,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hb2]
  have t10 : tickNatural program (state h2 (next+3) vr (next+2) next ar stack source 1823)=
      some ⟨state h2 (next+3) vr (next+2) next ar
        (⟨1824,.r3,⟨vr,next+2,next,ar⟩⟩::stack) source 1798,[],0⟩ := rfl
  have whole := NaturalRun.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5
    (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 run))))))))))
  refine ⟨[scratch]++[maskctx]++[queryctx]++e,root,vr,?_,?_,?_,?_⟩
  · simp [len]
  · convert whole using 1 <;> simp [state,List.append_assoc,Nat.add_assoc]
    omega
  · simpa only [h2,h1,h0,List.append_assoc] using rep
  · simpa only [h2,h1,h0,List.append_assoc] using lookup_extend sc2 e
end DirectedFlowCutGap.AvoidingDemandScan
