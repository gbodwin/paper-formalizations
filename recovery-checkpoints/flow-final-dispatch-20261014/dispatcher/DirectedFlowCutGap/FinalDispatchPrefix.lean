import DirectedFlowCutGap.FinalDispatchCalls

namespace DirectedFlowCutGap.FinalDispatch
set_option maxRecDepth 32768
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor

/-- Reuse the original demand list as the dispatcher's word-pair table. -/
theorem demand_table {n : ℕ} {heap : NaturalHeap} {p : ℕ}
    {xs : List DemandCollection.Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (pairs : DemandCollection.DemandList heap p xs)
    (encoded : List.Forall₂ (DemandCollection.EncodesDemand RowVertices.vertexLabel) xs ds) :
    WordPairTableRead.Table heap p
      (ds.map fun e => (RowVertices.vertexLabel e.1,RowVertices.vertexLabel e.2)) := by
  induction pairs generalizing ds with
  | nil hp => cases encoded;exact .nil hp
  | cons _ hp hx _ ih =>
    cases encoded with
    | cons he tail =>
      obtain ⟨sr,tr,hr,hs,ht⟩ := hx
      exact .cons hp hr (he.1 ▸ hs) (he.2 ▸ ht) (ih tail)

/-- Generate labels, construct the literal dispatch context and run the checked
original dispatch while its caller retains the three original roots. -/
theorem prepare_dispatch {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n)
    {xs : List DemandCollection.Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (DemandCollection.EncodesDemand RowVertices.vertexLabel) xs ds)
    {heap : NaturalHeap} {a b c d : ℕ}
    (table : WordPairTableRead.Table heap a (IndexedRationalRead.fields costs.toList))
    (graph : GraphAdjacencyProgram.Matrix heap b (GraphRelaxationRefinement.matrix adjacency))
    (pairs : DemandCollection.DemandList heap c xs)
    (next : ℕ) (dense : next=heap.length) (saved : Registers ℕ) (pc : Fin 13320)
    (stack : List (Frame ℕ 13320)) (source : Bits) :
    ∃ k ext root,k≤RowVertices.instructionBound n+dispatchSteps adjacency costs ds+8 ∧
      NaturalRun program k (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 13270) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      OriginalDispatch.Result (heap++ext) root
        (OriginalDispatch.encode RowVertices.vertexLabel (BinaryFractionalDispatch.dispatch adjacency ds costs).1) := by
  let frames := ⟨pc,.r3,saved⟩::stack
  have t0 : tickNatural program (state heap next a b c d frames source 13270)=
      some ⟨state heap next a b c d (⟨13271,.r3,⟨a,b,c,d⟩⟩::frames) source 12940,[],0⟩ := by rfl
  obtain ⟨kv,ev,vr,bv,vertexRun,vertices⟩ := vertex_call (ScalarAdditionRow.stored_of_table table)
    next b c d dense ⟨a,b,c,d⟩ 13271 frames source
  let h1 := heap++ev
  let n1 := next+ev.length
  let ep : NaturalHeap := [.pair a b,.pair vr n1]
  let h2 := h1++ep
  have nd : n1=h1.length := by simp [n1,h1,dense]
  have t1 : tickNatural program (state h1 n1 a b c vr frames source 13271)=
      some ⟨state (h1++[.pair a b]) (n1+1) a n1 c vr frames source 13272,[],0⟩ := by rfl
  have t2 : tickNatural program (state (h1++[.pair a b]) (n1+1) a n1 c vr frames source 13272)=
      some ⟨state h2 (n1+2) a (n1+1) c vr frames source 13273,[],0⟩ := by
    simp [tickNatural,program,state,h2,ep,Registers.get,Registers.set,allocateNatural,Recipe.cell,
      List.append_assoc,Nat.add_assoc]
  have t3 : tickNatural program (state h2 (n1+2) a (n1+1) c vr frames source 13273)=
      some ⟨state h2 (n1+2) c (n1+1) c vr frames source 13274,[],0⟩ := by rfl
  have t4 : tickNatural program (state h2 (n1+2) c (n1+1) c vr frames source 13274)=
      some ⟨state h2 (n1+2) c (n1+1) c vr
        (⟨13275,.r3,⟨c,n1+1,c,vr⟩⟩::frames) source 12898,[],0⟩ := by rfl
  have labels : GraphDiscoveryProgram.Vertices h1 vr (List.ofFn (RowVertices.vertexLabel (n:=n))) := by
    simpa only [List.ofFn_eq_map,RowVertices.labels_exact,Vector.length_toList] using vertices
  have context : OriginalDispatch.Context h2 (n1+1) (List.ofFn (RowVertices.vertexLabel (n:=n)))
      (IndexedRationalRead.fields costs.toList) (GraphRelaxationRefinement.matrix adjacency) := by
    refine ⟨vr,n1,a,b,?_,?_,GraphDiscoveryProgram.vertices_extend labels ep,
      BinaryIndexedPairRead.table_extend (BinaryIndexedPairRead.table_extend table ev) ep,
      KeptAdjacencyMatrix.matrix_of_graph
        (GraphAdjacencyProgram.matrix_extend (GraphAdjacencyProgram.matrix_extend graph ev) ep)⟩
    · simp [h2,ep,nd]
    · simp [h2,ep,nd]
  have demands : OriginalDispatch.Table h2 c
      (ds.map fun e => (RowVertices.vertexLabel e.1,RowVertices.vertexLabel e.2)) :=
    BinaryIndexedPairRead.table_extend (BinaryIndexedPairRead.table_extend (demand_table pairs encoded) ev) ep
  obtain ⟨ed,root,dispatchRun,rep⟩ := dispatch_call adjacency costs ds demands context
    (n1+2) c vr (by simp [h2,ep,nd]) ⟨c,n1+1,c,vr⟩ 13275 frames source
  have t5 : tickNatural program (state (h2++ed) (n1+2+ed.length) c (n1+1) c root frames source 13275)=
      some ⟨state (h2++ed) (n1+2+ed.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,frames,Registers.get,Registers.set]
  refine ⟨kv+(dispatchSteps adjacency costs ds+1)+6,ev++ep++ed,root,?_,?_,?_⟩
  · simp only [Vector.length_toList] at bv
    omega
  · have whole := NaturalRun.step t0 (run_append vertexRun (.step t1 (.step t2 (.step t3 (.step t4
      (run_append dispatchRun (.step t5 (.done _))))))))
    convert whole using 1 <;>
      simp [state,h1,h2,n1,ep,List.append_assoc,Nat.add_assoc]
  · simpa only [h2,h1,List.append_assoc] using rep
end DirectedFlowCutGap.FinalDispatch
