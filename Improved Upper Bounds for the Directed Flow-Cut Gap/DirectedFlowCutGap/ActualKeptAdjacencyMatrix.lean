import DirectedFlowCutGap.KeptAdjacencyMatrixExecution

namespace DirectedFlowCutGap.KeptAdjacencyMatrix
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor

theorem scan_bit {H A : ℕ} {rows : List Bits} {kept remaining : Bits}
    (initial : BitState 84) (bounded : initial.Bounded H A) (pc0 : initial.pc=82)
    (dense : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (hu : Matrix (eraseState initial).heap (eraseState initial).registers.a rows)
    (hc : Context (eraseState initial).heap (eraseState initial).registers.b remaining kept)
    (aligned : rows.length=remaining.length) (widths : ∀ u∈rows,u.length=kept.length) :
    ∃ charge out, Run program (steps kept rows remaining+1) charge initial [] out ∧
      Matrix (eraseState out).heap (eraseState out).registers.d (matrix kept rows remaining) ∧
      Matrix (eraseState out).heap (eraseState initial).registers.a rows ∧
      Context (eraseState out).heap (eraseState initial).registers.b remaining kept ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=83 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext ∧ ext.length=cells kept rows remaining) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 84 H A
        (inputSteps rows) := by
  have dense' : (eraseState initial).next=(eraseState initial).heap.length := by
    simpa [eraseState,State.map] using dense
  have start : state (eraseState initial).heap (eraseState initial).next
      (eraseState initial).registers.a (eraseState initial).registers.b (eraseState initial).registers.c
      (eraseState initial).registers.d (eraseState initial).stack initial.source 82=eraseState initial := by
    cases initial
    simp_all [eraseState,State.map,state]
  obtain ⟨ext,root,len,high,rep⟩ := scan hu hc aligned widths (eraseState initial).next
    (eraseState initial).registers.c (eraseState initial).registers.d dense'
    (eraseState initial).stack initial.source
  rw [start] at high
  have halt : tickNatural program (state ((eraseState initial).heap++ext)
      ((eraseState initial).next+ext.length) (eraseState initial).registers.a
      (eraseState initial).registers.b (eraseState initial).registers.c root
      (eraseState initial).stack initial.source 83)=none := by simp [tickNatural,state,program]
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
      (SupportSearchEncoding.complete_mono 84 H A _ _ (steps_bound kept rows remaining))⟩
  · simpa only [erase,state] using rep
  · rw [erase];exact GraphDiscoveryProgram.vertices_extend hu ext
  · rw [erase];exact context_extend hc ext
  · have h : (eraseState out).stack=(eraseState initial).stack := by rw [erase];rfl
    simpa [eraseState,State.map,empty] using h
  · have h : (eraseState out).pc=83 := by rw [erase];rfl
    exact h
  · rw [erase];rfl

end DirectedFlowCutGap.KeptAdjacencyMatrix
