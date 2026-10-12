import DirectedFlowCutGap.DemandQueryContext

namespace DirectedFlowCutGap.DemandCollection
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor
open GraphWalkExtension

theorem shortest_call {heap : NaturalHeap} {a b c : ℕ} {vs adjacency : List Bits}
    {values : List Fraction} {sw target u : Bits} (N : ℕ)
    (input : GraphDiscoveryProgram.Vertices heap a vs)
    (context : GraphDiscoveryProgram.GlobalContext heap b vs adjacency values sw target)
    (word : BoolList heap c u) (rows : N ≤ adjacency.length)
    (cols : ∀ (i : ℕ) (hi : i<N),N ≤ (adjacency[i]'(lt_of_lt_of_le hi rows)).length)
    (hv : ∀ v∈vs,value v<N) (ht : value target<N) (hc : ∀ v∈vs,value v<values.length)
    (valid : ∀ q,GraphDiscoveryProgram.minimize vs adjacency values sw target u=some q →
      ∀ w∈(CostedSupportProgram.edges vs adjacency q.edges sw target).map Prod.fst,value w<values.length)
    (next d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 1604)
    (stack : List (Frame ℕ 1604)) (source : Bits) :
    ∃ ext root,ext.length=GraphRecoveryController.cells vs adjacency values sw target u ∧
      NaturalRun program (GraphRecoveryController.steps vs adjacency values sw target u+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 1342) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      GraphDiscoveryProgram.StoredOption (heap++ext) root (GraphRecoveryController.result vs adjacency values sw target u) := by
  obtain ⟨ext,root,len,high,rep⟩ := GraphRecoveryController.shortest_high N
    (GraphRecoveryController.state heap next a b c d [] source 1342) rfl hn rfl input context word
    rows cols hv ht hc valid
  let frames := (⟨pc,.r3,saved⟩::stack)
  have mapped := ReferenceProgramLabels.run shortestLabel GraphRecoveryController.program program shortest_slots high
  have lifted := ReferenceProgramStack.run program frames mapped
  have body : NaturalRun program (GraphRecoveryController.steps vs adjacency values sw target u+1)
      (state heap next a b c d frames source 1342) []
      (state (heap++ext) (next+ext.length) a b c root frames source 1343) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,ReferenceProgramStack.state,
      GraphRecoveryController.state,shortestLabel,state] using lifted
  have ret : tickNatural program (state (heap++ext) (next+ext.length) a b c root frames source 1343)=
      some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,frames,Registers.get,Registers.set]
  exact ⟨ext,root,len,by simpa [Nat.add_assoc] using run_append body (.step ret (.done _)),rep⟩

theorem query_return {heap : NaturalHeap} {x : Demand} {global : ℕ} {vs adjacency : List Bits}
    {values : List Fraction} (N : ℕ) (demand : StoredDemand heap x)
    (context : GraphDiscoveryProgram.GlobalContext heap global vs adjacency values x.sourceWord x.targetWord)
    (rows : N ≤ adjacency.length)
    (cols : ∀ (i : ℕ) (hi : i<N),N ≤ (adjacency[i]'(lt_of_lt_of_le hi rows)).length)
    (hv : ∀ v∈vs,value v<N) (ht : value x.targetWord<N) (hc : ∀ v∈vs,value v<values.length)
    (valid : ∀ q,GraphDiscoveryProgram.minimize vs adjacency values x.sourceWord x.targetWord x.sourceWord=some q →
      ∀ w∈(CostedSupportProgram.edges vs adjacency q.edges x.sourceWord x.targetWord).map Prod.fst,value w<values.length)
    (next b c : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 1604)
    (stack : List (Frame ℕ 1604)) (source : Bits) :
    ∃ ext root,ext.length=queryCells vs adjacency values x ∧
      NaturalRun program (querySteps vs adjacency values x+8)
        (state heap next x.record b c global (⟨pc,.r3,saved⟩::stack) source 1592) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      GraphDiscoveryProgram.StoredOption (heap++ext) root (query vs adjacency values x) := by
  obtain ⟨sr,tr,hpair,hs,_⟩ := demand
  obtain ⟨target,bundle,er,mix,matrix,cost,hp,hb,hm,htarget,hvertices,hmatrix,hcost⟩ := context
  let frames := (⟨pc,.r3,saved⟩::stack)
  have context' : GraphDiscoveryProgram.GlobalContext heap global vs adjacency values x.sourceWord x.targetWord :=
    ⟨target,bundle,er,mix,matrix,cost,hp,hb,hm,htarget,hvertices,hmatrix,hcost⟩
  obtain ⟨ext,root,len,call,rep⟩ := shortest_call N hvertices context' hs rows cols hv ht hc valid
    next global hn ⟨er,global,sr,global⟩ 1597 frames source
  have t1592 : tickNatural program (state heap next x.record b c global frames source 1592)=
      some ⟨state heap next x.record global c global frames source 1593,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  have t1593 : tickNatural program (state heap next x.record global c global frames source 1593)=
      some ⟨state heap next x.record global sr global frames source 1594,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hpair]
  have t1594 : tickNatural program (state heap next x.record global sr global frames source 1594)=
      some ⟨state heap next bundle global sr global frames source 1595,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hp]
  have t1595 : tickNatural program (state heap next bundle global sr global frames source 1595)=
      some ⟨state heap next er global sr global frames source 1596,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hb]
  have t1596 : tickNatural program (state heap next er global sr global frames source 1596)=
      some ⟨state heap next er global sr global (⟨1597,.r3,⟨er,global,sr,global⟩⟩::frames) source 1342,[],0⟩ := by
    simp [tickNatural,program,state]
  have t1597 : tickNatural program (state (heap++ext) (next+ext.length) er global sr root frames source 1597)=
      some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,frames,Registers.get,Registers.set]
  refine ⟨ext,root,len,?_,rep⟩
  have all := run_append (.step t1592 (.step t1593 (.step t1594 (.step t1595 (.step t1596 call))))) (.step t1597 (.done _))
  convert all using 1 <;> simp [querySteps]

end DirectedFlowCutGap.DemandCollection
