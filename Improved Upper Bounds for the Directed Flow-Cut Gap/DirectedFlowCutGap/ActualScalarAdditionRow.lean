import DirectedFlowCutGap.ScalarAdditionRowBounds

namespace DirectedFlowCutGap.ScalarAdditionRow
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

/-- Each addition record and list cell is produced by this same physical run.
Both original inputs remain available, and the final terminal attempt is paid. -/
theorem row_bit (scalar : Fraction) {xs : List Fraction} {H A : ℕ}
    (initial : BitState 160) (bounded : initial.Bounded H A) (pc0 : initial.pc=158)
    (hn : value initial.next=initial.heap.length)
    (row : StoredList (eraseState initial).heap (eraseState initial).registers.a xs)
    (sc : Stored (eraseState initial).heap (eraseState initial).registers.b scalar)
    (empty : initial.stack=[]) :
    ∃ charge out,Run program (1+steps scalar xs) charge initial [] out ∧
      StoredList (eraseState out).heap (eraseState out).registers.d (result scalar xs) ∧
      StoredList (eraseState out).heap (eraseState initial).registers.a xs ∧
      Stored (eraseState out).heap (eraseState initial).registers.b scalar ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=159 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext ∧ ext.length=cells scalar xs) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 160 H A (inputSteps scalar xs) := by
  have hn' : (eraseState initial).next=(eraseState initial).heap.length := by
    simpa [eraseState,State.map] using hn
  have hs : (eraseState initial).stack=[] := by simp [eraseState,State.map,empty]
  obtain ⟨ext,root,len,high,rep⟩ := row_high scalar (eraseState initial) pc0 hn' row sc hs
  obtain ⟨charge,out,run,erase,_,_,source⟩ := polynomial_simulation bounded high
  have halt : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase] at obs
    have hn : tickNatural program
        (state ((eraseState initial).heap++ext) ((eraseState initial).next+ext.length)
          (eraseState initial).registers.a (eraseState initial).registers.b
          (eraseState initial).registers.c root [] (eraseState initial).source 159)=none := rfl
    rw [hn] at obs
    cases ht : tick program out with
    | none => rfl
    | some r => simp [ht] at obs
  have cost := (terminal_accounting run bounded halt).2
  have hb := steps_input_bound scalar xs
  have hm : completeBound 160 H A (1+steps scalar xs) ≤
      completeBound 160 H A (inputSteps scalar xs) := by
    unfold completeBound runBound stepBound
    gcongr
  refine ⟨charge,out,run,?_,?_,?_,source,?_,?_,⟨ext,?_,len⟩,halt,cost.trans hm⟩
  · rw [erase];exact rep
  · rw [erase];exact list_extend row ext
  · rw [erase];exact stored_extend sc ext
  · have h : (eraseState out).stack=[] := by rw [erase];rfl
    simpa [eraseState,State.map] using h
  · have h : (eraseState out).pc=159 := by rw [erase];rfl
    exact h
  · rw [erase];rfl
end DirectedFlowCutGap.ScalarAdditionRow
