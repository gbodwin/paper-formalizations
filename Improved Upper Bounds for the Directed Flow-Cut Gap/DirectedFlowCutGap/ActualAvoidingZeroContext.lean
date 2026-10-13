import DirectedFlowCutGap.AvoidingZeroContextExecution

namespace DirectedFlowCutGap.AvoidingZeroContext
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor

theorem scan_bit {H A : ℕ} {vs adjacency : List Bits} {sw target : Bits}
    (initial : BitState 64) (bounded : initial.Bounded H A) (pc0 : initial.pc=62)
    (dense : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (hu : GraphDiscoveryProgram.Vertices (eraseState initial).heap (eraseState initial).registers.a vs)
    (hc : Static (eraseState initial).heap (eraseState initial).registers.b adjacency sw target) :
    ∃ charge out, Run program (inputSteps vs) charge initial [] out ∧
      GraphDiscoveryProgram.GlobalContext (eraseState out).heap (eraseState out).registers.d
        vs adjacency (List.replicate vs.length BinaryRational.zero) sw target ∧
      GraphDiscoveryProgram.Vertices (eraseState out).heap (eraseState initial).registers.a vs ∧
      Static (eraseState out).heap (eraseState initial).registers.b adjacency sw target ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=63 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext ∧ ext.length=vs.length+14) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 64 H A
        (inputSteps vs) := by
  have dense' : (eraseState initial).next=(eraseState initial).heap.length := by
    simpa [eraseState,State.map] using dense
  have start : state (eraseState initial).heap (eraseState initial).next
      (eraseState initial).registers.a (eraseState initial).registers.b (eraseState initial).registers.c
      (eraseState initial).registers.d (eraseState initial).stack initial.source 62=eraseState initial := by
    cases initial
    simp_all [eraseState,State.map,state]
  obtain ⟨ext,root,len,high,rep⟩ := construct hu hc (eraseState initial).next
    (eraseState initial).registers.c (eraseState initial).registers.d dense'
    (eraseState initial).stack initial.source
  rw [start] at high
  have halt : tickNatural program (state ((eraseState initial).heap++ext)
      ((eraseState initial).next+ext.length) (eraseState initial).registers.a
      (eraseState initial).registers.b (eraseState initial).registers.c root
      (eraseState initial).stack initial.source 63)=none := by simp [tickNatural,state,program]
  obtain ⟨charge,out,run,erase,_,_,sourceOut⟩ := polynomial_simulation bounded high
  have stop : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase,halt] at obs
    cases h : tick program out with
    | none => rfl
    | some r => simp [h] at obs
  refine ⟨charge,out,run,?_,?_,?_,sourceOut,?_,?_,⟨ext,?_,len⟩,stop,
    (terminal_accounting run bounded stop).2⟩
  · simpa only [erase,state] using rep
  · rw [erase];exact GraphDiscoveryProgram.vertices_extend hu ext
  · rw [erase];exact static_extend hc ext
  · have h : (eraseState out).stack=(eraseState initial).stack := by rw [erase];rfl
    simpa [eraseState,State.map,empty] using h
  · have h : (eraseState out).pc=63 := by rw [erase];rfl
    exact h
  · rw [erase];rfl

end DirectedFlowCutGap.AvoidingZeroContext
