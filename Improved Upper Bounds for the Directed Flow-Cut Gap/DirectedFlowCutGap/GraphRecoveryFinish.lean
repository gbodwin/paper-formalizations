import DirectedFlowCutGap.GraphRecoveryCalls

namespace DirectedFlowCutGap.GraphRecoveryController
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor
open GraphWalkExtension

theorem finish_return {heap : NaturalHeap} {b d : ℕ} {vs adjacency : List Bits}
    {values : List Fraction} {sw target : Bits} {chosen : Option Walk} (N : ℕ)
    (context : GraphDiscoveryProgram.GlobalContext heap b vs adjacency values sw target)
    (candidate : GraphDiscoveryProgram.StoredOption heap d chosen)
    (rows : N ≤ adjacency.length)
    (cols : ∀ (i : ℕ) (hi : i<N),N ≤ (adjacency[i]'(lt_of_lt_of_le hi rows)).length)
    (hv : ∀ u∈vs,value u<N) (ht : value target<N)
    (valid : ∀ q,chosen=some q → ∀ w∈(CostedSupportProgram.edges vs adjacency q.edges sw target).map Prod.fst,
      value w<values.length)
    (next a c : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 1344)
    (stack : List (Frame ℕ 1344)) (source : Bits) :
    ∃ ext root,ext.length=finishCells vs adjacency values sw target chosen ∧
      NaturalRun program (finishSteps vs adjacency values sw target chosen)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 1313) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      GraphDiscoveryProgram.StoredOption (heap++ext) root
        (chosen.map (fun q => CostedSupportProgram.result vs adjacency q.edges sw target values)) := by
  let frames := (⟨pc,.r3,saved⟩::stack)
  cases chosen with
  | none =>
    change heap[d]?=some .nil at candidate
    have branch : tickNatural program (state heap next a b c d frames source 1313)=
        some ⟨state heap next a b c d frames source 1341,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,candidate,tagBranch]
    have ret : tickNatural program (state heap next a b c d frames source 1341)=
        some ⟨state heap next saved.a saved.b saved.c d stack source pc,[],0⟩ := by
      simp [tickNatural,program,state,frames,Registers.get,Registers.set]
    exact ⟨[],d,rfl,by simpa [finishSteps] using NaturalRun.step branch (.step ret (.done _)),by change (heap++[])[d]?=some .nil;simpa using candidate⟩
  | some q =>
    obtain ⟨ec,enumRoot,sourceRoot,scratch,lc,construct,verts,ctx,word⟩ :=
      build_context context candidate next a c hn frames source
    have dense : next+4=(heap++ec).length := by simp [hn,lc]
    obtain ⟨er,root,lr,recovery,rep⟩ := recovery_call N verts ctx word rows cols hv ht (valid q rfl)
      (next+4) scratch dense ⟨enumRoot,next+3,sourceRoot,scratch⟩ 1330 frames source
    obtain ⟨edgeRoot,costRoot,hrecord,_,_⟩ := candidate
    have branch : tickNatural program (state heap next a b c d frames source 1313)=
        some ⟨state heap next a b c d frames source 1314,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,hrecord,tagBranch]
    have call : tickNatural program (state (heap++ec) (next+4) enumRoot (next+3) sourceRoot scratch frames source 1329)=
        some ⟨state (heap++ec) (next+4) enumRoot (next+3) sourceRoot scratch
          (⟨1330,.r3,⟨enumRoot,next+3,sourceRoot,scratch⟩⟩::frames) source 1310,[],0⟩ := by
      simp [tickNatural,program,state]
    have ret : tickNatural program
        (state ((heap++ec)++er) (next+4+er.length) enumRoot (next+3) sourceRoot root frames source 1330)=
        some ⟨state ((heap++ec)++er) (next+4+er.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
      simp [tickNatural,program,state,frames,Registers.get,Registers.set]
    refine ⟨ec++er,root,by simp [finishCells,lc,lr,Nat.add_comm],?_,?_⟩
    · have all := run_append (.step branch construct) (.step call (run_append recovery (.step ret (.done _))))
      convert all using 1 <;> simp [finishSteps,lc,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm];omega
    · simpa only [Option.map_some,GraphDiscoveryProgram.StoredOption,
        GraphRelaxationProgram.StoredOption,List.append_assoc] using rep

end DirectedFlowCutGap.GraphRecoveryController
