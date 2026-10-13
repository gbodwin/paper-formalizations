import DirectedFlowCutGap.KeptMaskExecution

namespace DirectedFlowCutGap.KeptMask
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor

theorem scan_bit {H A : ℕ} {s t : Bits} {vs : List Bits} {zs : Bits}
    (initial : BitState 132) (bounded : initial.Bounded H A) (pc0 : initial.pc=130)
    (dense : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (hu : Vertices (eraseState initial).heap (eraseState initial).registers.a vs)
    (hc : Context (eraseState initial).heap (eraseState initial).registers.b s t zs)
    (aligned : vs.length=zs.length) :
    ∃ charge out, Run program (steps s t vs zs+1) charge initial [] out ∧
      BoolList (eraseState out).heap (eraseState out).registers.d (mask s t vs zs) ∧
      Vertices (eraseState out).heap (eraseState initial).registers.a vs ∧
      Context (eraseState out).heap (eraseState initial).registers.b s t zs ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=131 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext ∧ ext.length=cells s t vs zs) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 132 H A
        (inputSteps s t vs) := by
  have dense' : (eraseState initial).next=(eraseState initial).heap.length := by
    simpa [eraseState,State.map] using dense
  have start : state (eraseState initial).heap (eraseState initial).next
      (eraseState initial).registers.a (eraseState initial).registers.b (eraseState initial).registers.c
      (eraseState initial).registers.d (eraseState initial).stack initial.source 130=eraseState initial := by
    cases initial
    simp_all [eraseState,State.map,state]
  obtain ⟨ext,root,len,high,rep⟩ := scan hu hc aligned (eraseState initial).next
    (eraseState initial).registers.c (eraseState initial).registers.d dense'
    (eraseState initial).stack initial.source
  rw [start] at high
  have halt : tickNatural program (state ((eraseState initial).heap++ext)
      ((eraseState initial).next+ext.length) (eraseState initial).registers.a
      (eraseState initial).registers.b (eraseState initial).registers.c root
      (eraseState initial).stack initial.source 131)=none := by simp [tickNatural,state,program]
  obtain ⟨charge,out,run,erase,_,_,sourceOut⟩ := polynomial_simulation bounded high
  have stop : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase,halt] at obs
    cases h : tick program out with
    | none => rfl
    | some r => simp [h] at obs
  refine ⟨charge,out,run,?_,?_,?_,sourceOut,?_,?_,⟨ext,?_,len⟩,stop,
    (terminal_accounting run bounded stop).2.trans
      (SupportSearchEncoding.complete_mono 132 H A _ _ (steps_bound s t vs zs))⟩
  · simpa only [erase,state] using rep
  · rw [erase];exact GraphDiscoveryProgram.vertices_extend hu ext
  · rw [erase];exact context_extend hc ext
  · have h : (eraseState out).stack=(eraseState initial).stack := by rw [erase];rfl
    simpa [eraseState,State.map,empty] using h
  · have h : (eraseState out).pc=131 := by rw [erase];rfl
    exact h
  · rw [erase];rfl

end DirectedFlowCutGap.KeptMask
