import DirectedFlowCutGap.FractionWidthExecution
import DirectedFlowCutGap.ActualSupportSearch

namespace DirectedFlowCutGap.FractionWidthProgram
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal
open BooleanTableRead PackedBooleanConstructor

theorem width_bit {H A : ℕ} {q : BinaryRational.Fraction}
    (initial : BitState 128) (bounded : initial.Bounded H A) (pc0 : initial.pc=126)
    (dense : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (input : RationalComparisonProgram.Stored (eraseState initial).heap (eraseState initial).registers.a q) :
    ∃ charge out,Run program (steps q+1) charge initial [] out ∧
      BoolList (eraseState out).heap (eraseState out).registers.d (BinaryFractionalGuesses.fractionWidth q).1 ∧
      RationalComparisonProgram.Stored (eraseState out).heap (eraseState initial).registers.a q ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=127 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext ∧ ext.length=cells q) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 128 H A (inputSteps q) := by
  have dense' : (eraseState initial).next=(eraseState initial).heap.length := by
    simpa [eraseState,State.map] using dense
  have start : state (eraseState initial).heap (eraseState initial).next
      (eraseState initial).registers.a (eraseState initial).registers.b (eraseState initial).registers.c
      (eraseState initial).registers.d (eraseState initial).stack initial.source 126=eraseState initial := by
    cases initial
    simp_all [eraseState,State.map,state]
  obtain ⟨ext,root,len,high,rep⟩ := width input (eraseState initial).next
    (eraseState initial).registers.b (eraseState initial).registers.c (eraseState initial).registers.d
    dense' (eraseState initial).stack initial.source
  rw [start] at high
  have halt : tickNatural program (state ((eraseState initial).heap++ext)
      ((eraseState initial).next+ext.length) (eraseState initial).registers.a
      (eraseState initial).registers.b (eraseState initial).registers.c root
      (eraseState initial).stack initial.source 127)=none := by simp [tickNatural,state,program]
  obtain ⟨charge,out,run,erase,_,_,sourceOut⟩ := polynomial_simulation bounded high
  have stop : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase,halt] at obs
    cases h : tick program out with
    | none => rfl
    | some r => simp [h] at obs
  refine ⟨charge,out,run,?_,?_,sourceOut,?_,?_,⟨ext,?_,len⟩,stop,?_⟩
  · simpa only [erase,state] using rep
  · rw [erase];exact RationalComparisonProgram.stored_extend input ext
  · have h : (eraseState out).stack=(eraseState initial).stack := by rw [erase];rfl
    simpa [eraseState,State.map,empty] using h
  · have h : (eraseState out).pc=127 := by rw [erase];rfl
    exact h
  · rw [erase];rfl
  · exact (terminal_accounting run bounded stop).2.trans
      (SupportSearchEncoding.complete_mono 128 H A _ _ (steps_bound q))
end DirectedFlowCutGap.FractionWidthProgram
