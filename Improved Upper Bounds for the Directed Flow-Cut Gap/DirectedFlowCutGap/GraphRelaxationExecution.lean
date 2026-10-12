import DirectedFlowCutGap.GraphRelaxationScan
import DirectedFlowCutGap.GraphRelaxationBounds

/-! Same-run bit execution of the actual adjacency-driven relaxation scan.
The bound depends on the represented table length, word widths and index cap. -/
namespace DirectedFlowCutGap.GraphRelaxationProgram
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open GraphWalkExtension

theorem scan_high {adjacency : List Bits} {rows : List Fraction} {sw u : Bits} {xs : List Entry}
    (initial : NaturalState 532) (pc0 : initial.pc=530)
    (hn : initial.next=initial.heap.length) (empty : initial.stack=[])
    (input : Table initial.heap initial.registers.a xs)
    (context : Context initial.heap initial.registers.b adjacency rows u sw)
    (hi : value u<adjacency.length) (hc : value u<rows.length)
    (hcols : ∀ x∈xs,value x.1<(adjacency[value u]).length) :
    ∃ ext root,ext.length=cells adjacency rows sw u xs ∧
      NaturalRun program (steps adjacency rows sw u xs+1) initial []
        (state (initial.heap++ext) (initial.next+ext.length) initial.registers.a initial.registers.b
          initial.registers.c root [] initial.source 531) ∧
      StoredOption (initial.heap++ext) root (scan adjacency rows sw u xs) := by
  cases initial with
  | mk heap next regs stack pc source =>
    cases regs with
    | mk a b c d =>
      simp only at pc0 hn empty input context
      subst pc;subst stack
      obtain ⟨ext,root,len,core,rep⟩ := scan_return input context hi hc hcols next c d hn ⟨a,b,c,d⟩ 531 [] source
      have first : tickNatural program (state heap next a b c d [] source 530)=
          some ⟨state heap next a b c d [⟨531,.r3,⟨a,b,c,d⟩⟩] source 464,[],0⟩ := by
        simp [tickNatural,program,state]
      exact ⟨ext,root,len,by simpa [state] using NaturalRun.step first core,rep⟩

theorem scan_bit {adjacency : List Bits} {rows : List Fraction} {sw u : Bits} {xs : List Entry}
    {H A : ℕ} (initial : BitState 532) (bounded : initial.Bounded H A) (pc0 : initial.pc=530)
    (hn : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (input : Table (eraseState initial).heap (eraseState initial).registers.a xs)
    (context : Context (eraseState initial).heap (eraseState initial).registers.b adjacency rows u sw)
    (hi : value u<adjacency.length) (hc : value u<rows.length)
    (hcols : ∀ x∈xs,value x.1<(adjacency[value u]).length)
    (B N : ℕ) (hB : 1 ≤ B) (hr : ∀ q∈rows,StoredBounded q B)
    (hu : u.length ≤ B) (iu : value u ≤ N) (hx : ∀ x∈xs,EntryBound B N x) :
    ∃ charge out,Run program (steps adjacency rows sw u xs+1) charge initial [] out ∧
      StoredOption (eraseState out).heap (eraseState out).registers.d (scan adjacency rows sw u xs) ∧
      Table (eraseState out).heap (eraseState initial).registers.a xs ∧
      Context (eraseState out).heap (eraseState initial).registers.b adjacency rows u sw ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=531 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext ∧ ext.length=cells adjacency rows sw u xs) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 532 H A (instructionBound xs.length B N sw.length) := by
  have hn' : (eraseState initial).next=(eraseState initial).heap.length := by simpa [eraseState,State.map] using hn
  have empty' : (eraseState initial).stack=[] := by simp [eraseState,State.map,empty]
  obtain ⟨ext,root,len,high,rep⟩ := scan_high (eraseState initial) pc0 hn' empty' input context hi hc hcols
  obtain ⟨charge,out,run,erase,_,_,src⟩ := polynomial_simulation bounded high
  have stop : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase] at obs
    have halt : tickNatural program
        (state ((eraseState initial).heap++ext) ((eraseState initial).next+ext.length)
          (eraseState initial).registers.a (eraseState initial).registers.b
          (eraseState initial).registers.c root [] (eraseState initial).source 531)=none := by
      simp [tickNatural,program,state]
    rw [halt] at obs
    cases ht : tick program out with
    | none => rfl
    | some x => simp [ht] at obs
  have cost := (terminal_accounting run bounded stop).2
  have hs := steps_bound adjacency rows sw u xs B N hB hr hc hu iu hx
  have hm : completeBound 532 H A (steps adjacency rows sw u xs+1) ≤ 
      completeBound 532 H A (instructionBound xs.length B N sw.length) := by
    unfold completeBound runBound stepBound
    gcongr
  refine ⟨charge,out,run,?_,?_,?_,by simpa [state,eraseState,State.map] using src,
    ?_,?_,⟨ext,?_,len⟩,stop,cost.trans hm⟩
  · rw [erase];exact rep
  · rw [erase];exact table_extend input ext
  · rw [erase];exact context_extend context ext
  · have h : (eraseState out).stack=[] := by rw [erase];rfl
    simpa [eraseState,State.map] using h
  · have h : (eraseState out).pc=531 := by rw [erase];rfl
    exact h
  · rw [erase];rfl

end DirectedFlowCutGap.GraphRelaxationProgram
