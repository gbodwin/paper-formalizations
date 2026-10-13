import DirectedFlowCutGap.EmptyDemandScanExecution

namespace DirectedFlowCutGap.EmptyDemandScan
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor

theorem scan_bit {H A : ℕ} {ds : List (Bits × Bits)} {rows : List Bits}
    (initial : BitState 160) (bounded : initial.Bounded H A) (pc0 : initial.pc=158)
    (dense : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (hu : Table (eraseState initial).heap (eraseState initial).registers.a ds)
    (hc : GraphAdjacencyProgram.Matrix (eraseState initial).heap (eraseState initial).registers.b rows)
    (valid : ∀ e∈ds,Valid rows e) :
    ∃ charge out, Run program (steps rows ds+1) charge initial [] out ∧
      Result (eraseState out).heap (eraseState out).registers.d (result rows ds) ∧
      Table (eraseState out).heap (eraseState initial).registers.a ds ∧
      GraphAdjacencyProgram.Matrix (eraseState out).heap (eraseState initial).registers.b rows ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=159 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext ∧ ext.length=cells rows ds) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 160 H A
        (inputSteps rows ds) := by
  have dense' : (eraseState initial).next=(eraseState initial).heap.length := by
    simpa [eraseState,State.map] using dense
  have start : state (eraseState initial).heap (eraseState initial).next
      (eraseState initial).registers.a (eraseState initial).registers.b (eraseState initial).registers.c
      (eraseState initial).registers.d (eraseState initial).stack initial.source 158=eraseState initial := by
    cases initial
    simp_all [eraseState,State.map,state]
  obtain ⟨ext,root,len,high,rep⟩ := scan hu hc valid (eraseState initial).next
    (eraseState initial).registers.c (eraseState initial).registers.d dense'
    (eraseState initial).stack initial.source
  rw [start] at high
  have halt : tickNatural program (state ((eraseState initial).heap++ext)
      ((eraseState initial).next+ext.length) (eraseState initial).registers.a
      (eraseState initial).registers.b (eraseState initial).registers.c root
      (eraseState initial).stack initial.source 159)=none := by simp [tickNatural,state,program]
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
      (SupportSearchEncoding.complete_mono 160 H A _ _ (steps_bound rows ds valid))⟩
  · simpa only [erase,state] using rep
  · rw [erase];exact BinaryIndexedPairRead.table_extend hu ext
  · rw [erase];exact GraphAdjacencyProgram.matrix_extend hc ext
  · have h : (eraseState out).stack=(eraseState initial).stack := by rw [erase];rfl
    simpa [eraseState,State.map,empty] using h
  · have h : (eraseState out).pc=159 := by rw [erase];rfl
    exact h
  · rw [erase];rfl

end DirectedFlowCutGap.EmptyDemandScan
