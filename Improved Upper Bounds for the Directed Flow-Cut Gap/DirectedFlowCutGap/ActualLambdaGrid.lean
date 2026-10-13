import DirectedFlowCutGap.LambdaGridExecution
import DirectedFlowCutGap.ActualSupportSearch

namespace DirectedFlowCutGap.LambdaGridProgram
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal
open BooleanTableRead PackedBooleanConstructor RationalComparisonProgram

theorem lambda_bit {H A : ℕ} {rows : List Fraction} {index exponent : Bits}
    (initial : BitState 1040) (bounded : initial.Bounded H A) (pc0 : initial.pc=1038)
    (dense : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (table : WordPairTableRead.Table (eraseState initial).heap (eraseState initial).registers.a (IndexedRationalRead.fields rows))
    (idx : BoolList (eraseState initial).heap (eraseState initial).registers.b index)
    (exp : BoolList (eraseState initial).heap (eraseState initial).registers.c exponent)
    (valid : value index<rows.length) :
    ∃ charge out,Run program (steps rows index exponent+1) charge initial [] out ∧
      Stored (eraseState out).heap (eraseState out).registers.d (result rows index exponent) ∧
      WordPairTableRead.Table (eraseState out).heap (eraseState initial).registers.a (IndexedRationalRead.fields rows) ∧
      BoolList (eraseState out).heap (eraseState initial).registers.b index ∧
      BoolList (eraseState out).heap (eraseState initial).registers.c exponent ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=1039 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext ∧ ext.length=cells rows index exponent) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 1040 H A (inputSteps rows index exponent) := by
  have dense' : (eraseState initial).next=(eraseState initial).heap.length := by
    simpa [eraseState,State.map] using dense
  have start : state (eraseState initial).heap (eraseState initial).next
      (eraseState initial).registers.a (eraseState initial).registers.b (eraseState initial).registers.c
      (eraseState initial).registers.d (eraseState initial).stack initial.source 1038=eraseState initial := by
    cases initial
    simp_all [eraseState,State.map,state]
  obtain ⟨ext,root,len,high,rep⟩ := compute table idx exp valid (eraseState initial).next (eraseState initial).registers.d dense' (eraseState initial).stack initial.source
  rw [start] at high
  have halt : tickNatural program (state ((eraseState initial).heap++ext)
      ((eraseState initial).next+ext.length) (eraseState initial).registers.a
      (eraseState initial).registers.b (eraseState initial).registers.c root
      (eraseState initial).stack initial.source 1039)=none := by rfl
  obtain ⟨charge,out,run,erase,_,_,sourceOut⟩ := polynomial_simulation bounded high
  have stop : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase,halt] at obs
    cases h : tick program out with
    | none => rfl
    | some r => simp [h] at obs
  refine ⟨charge,out,run,?_,?_,?_,?_,sourceOut,?_,?_,⟨ext,?_,len⟩,stop,?_⟩
  · simpa only [erase,state] using rep
  · rw [erase];exact BinaryIndexedPairRead.table_extend table ext
  · rw [erase];exact boolList_extend idx ext
  · rw [erase];exact boolList_extend exp ext
  · have h : (eraseState out).stack=(eraseState initial).stack := by rw [erase];rfl
    simpa [eraseState,State.map,empty] using h
  · have h : (eraseState out).pc=1039 := by rw [erase];rfl
    exact h
  · rw [erase];rfl
  · exact (terminal_accounting run bounded stop).2.trans
      (SupportSearchEncoding.complete_mono 1040 H A _ _ (steps_bound rows index exponent valid))
end DirectedFlowCutGap.LambdaGridProgram
