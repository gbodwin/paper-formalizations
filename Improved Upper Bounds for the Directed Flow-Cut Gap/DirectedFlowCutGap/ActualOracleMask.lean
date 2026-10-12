import DirectedFlowCutGap.OracleMaskBounds

/-! The same physical mask-construction run retains its initial heap and pays
its terminal halt. It consumes real retained edges and endpoint words. -/
namespace DirectedFlowCutGap.OracleMask
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor GraphWalkExtension

theorem mask_high {vs : List Bits} {s t : Bits} {es : List (Bits × Bits)}
    (initial : NaturalState 160) (pc0 : initial.pc=150)
    (hn : initial.next=initial.heap.length) (empty : initial.stack=[])
    (input : GraphDiscoveryProgram.Vertices initial.heap initial.registers.a vs)
    (context : Context initial.heap initial.registers.b s t es) :
    ∃ ext root,ext.length=cells s t es vs ∧ NaturalRun program (steps s t es vs+1) initial []
      (state (initial.heap++ext) (initial.next+ext.length) initial.registers.a initial.registers.b
        initial.registers.c root [] initial.source 151) ∧
      BoolList (initial.heap++ext) root (mask s t es vs) := by
  cases initial with
  | mk heap next regs stack pc source =>
    cases regs with
    | mk a b c d =>
      simp only at pc0 hn empty input context
      subst pc;subst stack
      obtain ⟨ext,root,len,body,rep⟩ := mask_return input next b c d hn context ⟨a,b,c,d⟩ 151 [] source
      have first : tickNatural program (state heap next a b c d [] source 150)=
          some ⟨state heap next a b c d [⟨151,.r3,⟨a,b,c,d⟩⟩] source 120,[],0⟩ := by
        simp [tickNatural,program,state]
      exact ⟨ext,root,len,by simpa [state] using NaturalRun.step first body,rep⟩

theorem mask_bit {vs : List Bits} {s t : Bits} {es : List (Bits × Bits)} {H A : ℕ}
    (initial : BitState 160) (bounded : initial.Bounded H A) (pc0 : initial.pc=150)
    (hn : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (input : GraphDiscoveryProgram.Vertices (eraseState initial).heap (eraseState initial).registers.a vs)
    (context : Context (eraseState initial).heap (eraseState initial).registers.b s t es)
    (W : ℕ) (hs : s.length≤W) (ht : t.length≤W) (he : widths W es)
    (hv : ∀ u∈vs,u.length≤W) :
    ∃ charge out,Run program (steps s t es vs+1) charge initial [] out ∧
      BoolList (eraseState out).heap (eraseState out).registers.d (mask s t es vs) ∧
      GraphDiscoveryProgram.Vertices (eraseState out).heap (eraseState initial).registers.a vs ∧
      Context (eraseState out).heap (eraseState initial).registers.b s t es ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=151 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext ∧ ext.length=cells s t es vs) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations≤completeBound 160 H A (instructionBound vs.length es.length W) := by
  have hn' : (eraseState initial).next=(eraseState initial).heap.length := by simpa [eraseState,State.map] using hn
  have empty' : (eraseState initial).stack=[] := by simp [eraseState,State.map,empty]
  obtain ⟨ext,root,len,high,rep⟩ := mask_high (eraseState initial) pc0 hn' empty' input context
  obtain ⟨charge,out,run,erase,_,_,src⟩ := polynomial_simulation bounded high
  have stop : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase] at obs
    have halt : tickNatural program
        (state ((eraseState initial).heap++ext) ((eraseState initial).next+ext.length)
          (eraseState initial).registers.a (eraseState initial).registers.b
          (eraseState initial).registers.c root [] (eraseState initial).source 151)=none := by
      simp [tickNatural,program,state]
    rw [halt] at obs
    cases htick : tick program out with
    | none => rfl
    | some x => simp [htick] at obs
  refine ⟨charge,out,run,?_,?_,?_,by simpa [state,eraseState,State.map] using src,
    ?_,?_,⟨ext,?_,len⟩,stop,?_⟩
  · rw [erase];exact rep
  · rw [erase];exact GraphDiscoveryProgram.vertices_extend input ext
  · rw [erase];exact context_extend context ext
  · have h : (eraseState out).stack=[] := by rw [erase];rfl
    simpa [eraseState,State.map] using h
  · have h : (eraseState out).pc=151 := by rw [erase];rfl
    exact h
  · rw [erase];rfl
  · exact (terminal_accounting run bounded stop).2.trans
      (SupportSearchEncoding.complete_mono 160 H A _ _ (steps_le hs ht he hv))

end DirectedFlowCutGap.OracleMask
