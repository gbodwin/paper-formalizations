import DirectedFlowCutGap.MinimumShiftExecution

namespace DirectedFlowCutGap.MinimumShift
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal
open BooleanTableRead PackedBooleanConstructor

theorem shifted_bit {H A n : ℕ} (costs : BinaryFractionalRows.Row n) {exponent : Bits}
    (initial : BitState 1560) (bounded : initial.Bounded H A) (pc0 : initial.pc=1558)
    (dense : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (table : WordPairTableRead.Table (eraseState initial).heap (eraseState initial).registers.a (IndexedRationalRead.fields costs.toList))
    (exp : BoolList (eraseState initial).heap (eraseState initial).registers.c exponent) :
    ∃ k charge out,k ≤ inputSteps costs.toList exponent ∧ Run program k charge initial [] out ∧
      Result (eraseState out).heap (eraseState out).registers.d (result costs exponent) ∧
      WordPairTableRead.Table (eraseState out).heap (eraseState initial).registers.a (IndexedRationalRead.fields costs.toList) ∧
      BoolList (eraseState out).heap (eraseState initial).registers.c exponent ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=1559 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 1560 H A (inputSteps costs.toList exponent) := by
  have dense' : (eraseState initial).next=(eraseState initial).heap.length := by
    simpa [eraseState,State.map] using dense
  have start : state (eraseState initial).heap (eraseState initial).next
      (eraseState initial).registers.a (eraseState initial).registers.b (eraseState initial).registers.c
      (eraseState initial).registers.d (eraseState initial).stack initial.source 1558=eraseState initial := by
    cases initial
    simp_all [eraseState,State.map,state]
  obtain ⟨k,ext,root,hk,high,rep⟩ := compute costs table exp (eraseState initial).next
    (eraseState initial).registers.b (eraseState initial).registers.d
    dense' (eraseState initial).stack initial.source
  rw [start] at high
  have halt : tickNatural program (state ((eraseState initial).heap++ext)
      ((eraseState initial).next+ext.length) (eraseState initial).registers.a
      (eraseState initial).registers.b (eraseState initial).registers.c root
      (eraseState initial).stack initial.source 1559)=none := by simp [tickNatural,state,program]
  obtain ⟨charge,out,run,erase,_,_,sourceOut⟩ := polynomial_simulation bounded high
  have stop : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase,halt] at obs
    cases h : tick program out with
    | none => rfl
    | some r => simp [h] at obs
  refine ⟨k,charge,out,hk,run,?_,?_,?_,sourceOut,?_,?_,⟨ext,?_⟩,stop,?_⟩
  · simpa only [erase,state] using rep
  · rw [erase];exact BinaryIndexedPairRead.table_extend table ext
  · rw [erase];exact boolList_extend exp ext
  · have h : (eraseState out).stack=(eraseState initial).stack := by rw [erase];rfl
    simpa [eraseState,State.map,empty] using h
  · have h : (eraseState out).pc=1559 := by rw [erase];rfl
    exact h
  · rw [erase];rfl
  · exact (terminal_accounting run bounded stop).2.trans
      (SupportSearchEncoding.complete_mono 1560 H A _ _ hk)

end DirectedFlowCutGap.MinimumShift
