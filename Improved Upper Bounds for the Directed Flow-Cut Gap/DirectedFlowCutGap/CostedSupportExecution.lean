import DirectedFlowCutGap.CostedSupportContinuation

namespace DirectedFlowCutGap.CostedSupportProgram
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor
open GraphWalkExtension

theorem wrapped_search {heap : NaturalHeap} {a b c : ℕ} {vs adjacency : List Bits}
    {es : List (Bits×Bits)} {sw target : Bits} {values : List Fraction} (N : ℕ)
    (vertices : SupportRecoveryProgram.Vertices heap a vs)
    (context : Context heap b vs adjacency es target values sw) (word : BoolList heap c sw)
    (rows : N ≤ adjacency.length)
    (cols : ∀ (i : ℕ) (hi : i<N),N ≤ (adjacency[i]'(lt_of_lt_of_le hi rows)).length)
    (hv : ∀ u∈vs,value u<N) (ht : value target<N)
    (next d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 592)
    (stack : List (Frame ℕ 592)) (source : Bits) :
    ∃ ext root,ext.length=SupportRecoveryProgram.searchCells vs adjacency es sw target ∧
      NaturalRun program (SupportRecoveryProgram.searchSteps vs adjacency es sw target+5)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 580) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      EdgeList (heap++ext) root (edges vs adjacency es sw target) := by
  obtain ⟨searchRoot,costRoot,hctx,hsearch,_⟩ := context
  let frames := (⟨pc,.r3,saved⟩::stack)
  obtain ⟨ext,root,len,body,rep⟩ := search_call N vertices hsearch word rows cols hv ht next d hn
    ⟨a,searchRoot,c,d⟩ 582 frames source
  have t580 : tickNatural program (state heap next a b c d frames source 580)=
      some ⟨state heap next a searchRoot c d frames source 581,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hctx]
  have t581 : tickNatural program (state heap next a searchRoot c d frames source 581)=
      some ⟨state heap next a searchRoot c d (⟨582,.r3,⟨a,searchRoot,c,d⟩⟩::frames) source 270,[],0⟩ := by
    simp [tickNatural,program,state]
  have t582 : tickNatural program (state (heap++ext) (next+ext.length) a searchRoot c root frames source 582)=
      some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,frames,Registers.get,Registers.set]
  have preRun : NaturalRun program 2 (state heap next a b c d frames source 580) []
      (state heap next a searchRoot c d (⟨582,.r3,⟨a,searchRoot,c,d⟩⟩::frames) source 270) :=
    .step t580 (.step t581 (.done _))
  refine ⟨ext,root,len,?_,rep⟩
  have hc : SupportRecoveryProgram.searchSteps vs adjacency es sw target+5=
      2+(SupportRecoveryProgram.searchSteps vs adjacency es sw target+2+1) := by omega
  rw [hc]
  exact run_append preRun (run_append body (.step t582 (.done _)))

theorem recover_return {heap : NaturalHeap} {a b c : ℕ} {vs adjacency : List Bits}
    {es : List (Bits×Bits)} {sw target : Bits} {values : List Fraction} (N : ℕ)
    (vertices : SupportRecoveryProgram.Vertices heap a vs)
    (context : Context heap b vs adjacency es target values sw) (word : BoolList heap c sw)
    (rows : N ≤ adjacency.length)
    (cols : ∀ (i : ℕ) (hi : i<N),N ≤ (adjacency[i]'(lt_of_lt_of_le hi rows)).length)
    (hv : ∀ u∈vs,value u<N) (ht : value target<N)
    (valid : ∀ w∈(edges vs adjacency es sw target).map Prod.fst,value w<values.length)
    (next d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 592)
    (stack : List (Frame ℕ 592)) (source : Bits) :
    ∃ ext root,ext.length=cells vs adjacency es sw target values ∧
      NaturalRun program (steps vs adjacency es sw target values)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 576) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      StoredWalk (heap++ext) root (result vs adjacency es sw target values) := by
  let frames := (⟨pc,.r3,saved⟩::stack)
  obtain ⟨er,path,lr,search,edgesRep⟩ := wrapped_search N vertices context word rows cols hv ht
    next d hn ⟨a,b,c,d⟩ 577 frames source
  obtain ⟨ec,root,lc,cost,rep⟩ := cost_return (context_extend context er) edgesRep valid
    (next+er.length) a c (by simp [hn]) saved pc stack source
  have first : tickNatural program (state heap next a b c d frames source 576)=
      some ⟨state heap next a b c d (⟨577,.r3,⟨a,b,c,d⟩⟩::frames) source 580,[],0⟩ := by
    simp [tickNatural,program,state]
  refine ⟨er++ec,root,by simp [cells,lr,lc];omega,?_,?_⟩
  · have all := run_append (.step first search) cost
    convert all using 1 <;> simp [steps,List.append_assoc,Nat.add_assoc];omega
  · simpa only [result,List.append_assoc] using rep

theorem recover_high {vs adjacency : List Bits} {es : List (Bits×Bits)} {sw target : Bits}
    {values : List Fraction} (N : ℕ) (initial : NaturalState 592) (pc0 : initial.pc=590)
    (hn : initial.next=initial.heap.length) (empty : initial.stack=[])
    (vertices : SupportRecoveryProgram.Vertices initial.heap initial.registers.a vs)
    (context : Context initial.heap initial.registers.b vs adjacency es target values sw)
    (word : BoolList initial.heap initial.registers.c sw) (rows : N ≤ adjacency.length)
    (cols : ∀ (i : ℕ) (hi : i<N),N ≤ (adjacency[i]'(lt_of_lt_of_le hi rows)).length)
    (hv : ∀ u∈vs,value u<N) (ht : value target<N)
    (valid : ∀ w∈(edges vs adjacency es sw target).map Prod.fst,value w<values.length) :
    ∃ ext root,ext.length=cells vs adjacency es sw target values ∧
      NaturalRun program (steps vs adjacency es sw target values+1) initial []
        (state (initial.heap++ext) (initial.next+ext.length) initial.registers.a initial.registers.b
          initial.registers.c root [] initial.source 591) ∧
      StoredWalk (initial.heap++ext) root (result vs adjacency es sw target values) := by
  cases initial with
  | mk heap next regs stack pc source =>
    cases regs with
    | mk a b c d =>
      simp only at pc0 hn empty vertices context word
      subst pc;subst stack
      obtain ⟨ext,root,len,body,rep⟩ := recover_return N vertices context word rows cols hv ht valid
        next d hn ⟨a,b,c,d⟩ 591 [] source
      have first : tickNatural program (state heap next a b c d [] source 590)=
          some ⟨state heap next a b c d [⟨591,.r3,⟨a,b,c,d⟩⟩] source 576,[],0⟩ := by
        simp [tickNatural,program,state]
      exact ⟨ext,root,len,by simpa [state] using NaturalRun.step first body,rep⟩

end DirectedFlowCutGap.CostedSupportProgram
