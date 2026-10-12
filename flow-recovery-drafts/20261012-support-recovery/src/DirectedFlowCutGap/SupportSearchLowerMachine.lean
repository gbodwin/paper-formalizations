import DirectedFlowCutGap.SupportSearchExecution

/-! The same lower-machine run preserves the input representation and pays its
single terminal halt. Numerical input-size bounds are a separate theorem. -/
namespace DirectedFlowCutGap.SupportRecoveryProgram
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor GraphWalkExtension

theorem search_high {vertices adjacency : List Bits} {es : List (Bits×Bits)} {sw target : Bits}
    (N : ℕ) (initial : NaturalState 280) (pc0 : initial.pc=270)
    (hn : initial.next=initial.heap.length) (empty : initial.stack=[])
    (input : Vertices initial.heap initial.registers.a vertices)
    (context : StoredGlobalContext initial.heap initial.registers.b vertices adjacency es target)
    (word : BoolList initial.heap initial.registers.c sw) (rows : N≤adjacency.length)
    (cols : ∀ (i : ℕ) (hi : i<N), N≤(adjacency[i]'(lt_of_lt_of_le hi rows)).length)
    (hv : ∀ u∈vertices,value u<N) (ht : value target<N) :
    ∃ ext root,ext.length=searchCells vertices adjacency es sw target ∧
      NaturalRun program (searchSteps vertices adjacency es sw target+1) initial []
        (state (initial.heap++ext) (initial.next+ext.length) initial.registers.a initial.registers.b
          initial.registers.c root [] initial.source 279) ∧
      EdgeList (initial.heap++ext) root (search vertices adjacency es sw target) := by
  cases initial with
  | mk heap next regs stack pc source =>
    cases regs with
    | mk a b c d =>
      simp only at pc0 hn empty input context word
      subst pc;subst stack
      obtain ⟨ext,root,len,body,rep⟩ := search_return N input context word rows cols hv ht
        next d hn ⟨a,b,c,d⟩ 279 [] source
      have first : tickNatural program (state heap next a b c d [] source 270)=
          some ⟨state heap next a b c d [⟨279,.r3,⟨a,b,c,d⟩⟩] source 260,[],0⟩ := by
        simp [tickNatural,program,state]
      exact ⟨ext,root,len,by simpa [state] using NaturalRun.step first body,rep⟩

theorem search_bit {vertices adjacency : List Bits} {es : List (Bits×Bits)} {sw target : Bits}
    {H A : ℕ} (N : ℕ) (initial : BitState 280) (bounded : initial.Bounded H A)
    (pc0 : initial.pc=270) (hn : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (input : Vertices (eraseState initial).heap (eraseState initial).registers.a vertices)
    (context : StoredGlobalContext (eraseState initial).heap (eraseState initial).registers.b vertices adjacency es target)
    (word : BoolList (eraseState initial).heap (eraseState initial).registers.c sw)
    (rows : N≤adjacency.length) (cols : ∀ (i : ℕ) (hi : i<N), N≤(adjacency[i]'(lt_of_lt_of_le hi rows)).length)
    (hv : ∀ u∈vertices,value u<N) (ht : value target<N) :
    ∃ charge out,Run program (searchSteps vertices adjacency es sw target+1) charge initial [] out ∧
      EdgeList (eraseState out).heap (eraseState out).registers.d (search vertices adjacency es sw target) ∧
      Vertices (eraseState out).heap (eraseState initial).registers.a vertices ∧
      StoredGlobalContext (eraseState out).heap (eraseState initial).registers.b vertices adjacency es target ∧
      BoolList (eraseState out).heap (eraseState initial).registers.c sw ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=279 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext ∧
        ext.length=searchCells vertices adjacency es sw target) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations≤completeBound 280 H A (searchSteps vertices adjacency es sw target+1) := by
  have hn' : (eraseState initial).next=(eraseState initial).heap.length := by simpa [eraseState,State.map] using hn
  have empty' : (eraseState initial).stack=[] := by simp [eraseState,State.map,empty]
  obtain ⟨ext,root,len,high,rep⟩ := search_high N (eraseState initial) pc0 hn' empty' input context word rows cols hv ht
  obtain ⟨charge,out,run,erase,_,_,src⟩ := polynomial_simulation bounded high
  have stop : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase] at obs
    have halt : tickNatural program
        (state ((eraseState initial).heap++ext) ((eraseState initial).next+ext.length)
          (eraseState initial).registers.a (eraseState initial).registers.b
          (eraseState initial).registers.c root [] (eraseState initial).source 279)=none := by
      simp [tickNatural,program,state]
    rw [halt] at obs
    cases htick : tick program out with
    | none => rfl
    | some x => simp [htick] at obs
  refine ⟨charge,out,run,?_,?_,?_,?_,by simpa [state,eraseState,State.map] using src,
    ?_,?_,⟨ext,?_,len⟩,stop,(terminal_accounting run bounded stop).2⟩
  · rw [erase];exact rep
  · rw [erase];exact GraphDiscoveryProgram.vertices_extend input ext
  · rw [erase];exact globalContext_extend context ext
  · rw [erase];exact boolList_extend word ext
  · have h : (eraseState out).stack=[] := by rw [erase];rfl
    simpa [eraseState,State.map] using h
  · have h : (eraseState out).pc=279 := by rw [erase];rfl
    exact h
  · rw [erase];rfl

end DirectedFlowCutGap.SupportRecoveryProgram
