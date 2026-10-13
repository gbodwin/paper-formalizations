import DirectedFlowCutGap.BinaryMaximumExecution
import DirectedFlowCutGap.ActualSupportSearch

namespace DirectedFlowCutGap.BinaryMaximumProgram
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal
open BooleanTableRead PackedBooleanConstructor

theorem maximum_bit {H A : ℕ} {xs ys : Bits}
    (initial : BitState 56) (bounded : initial.Bounded H A) (pc0 : initial.pc=54)
    (dense : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (left : BoolList (eraseState initial).heap (eraseState initial).registers.a xs)
    (right : BoolList (eraseState initial).heap (eraseState initial).registers.b ys) :
    ∃ charge out,Run program (steps xs ys+1) charge initial [] out ∧
      BoolList (eraseState out).heap (eraseState out).registers.d (BinaryFractionalGuesses.maximum xs ys).1 ∧
      BoolList (eraseState out).heap (eraseState initial).registers.a xs ∧
      BoolList (eraseState out).heap (eraseState initial).registers.b ys ∧
      (eraseState out).registers.d=pointer xs ys (eraseState initial).registers.a (eraseState initial).registers.b ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=55 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext ∧ ext.length=BinaryComparisonProgram.cells xs ys+1) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 56 H A (inputSteps xs ys) := by
  have dense' : (eraseState initial).next=(eraseState initial).heap.length := by
    simpa [eraseState,State.map] using dense
  have start : state (eraseState initial).heap (eraseState initial).next
      (eraseState initial).registers.a (eraseState initial).registers.b (eraseState initial).registers.c
      (eraseState initial).registers.d (eraseState initial).stack initial.source 54=eraseState initial := by
    cases initial
    simp_all [eraseState,State.map,state]
  obtain ⟨ext,len,high,rep⟩ := maximum left right (eraseState initial).next
    (eraseState initial).registers.c (eraseState initial).registers.d
    dense' (eraseState initial).stack initial.source
  rw [start] at high
  have halt : tickNatural program (state ((eraseState initial).heap++ext)
      ((eraseState initial).next+ext.length) (eraseState initial).registers.a
      (eraseState initial).registers.b (eraseState initial).registers.c (pointer xs ys (eraseState initial).registers.a (eraseState initial).registers.b)
      (eraseState initial).stack initial.source 55)=none := by simp [tickNatural,state,program]
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
  · rw [erase];exact boolList_extend left ext
  · rw [erase];exact boolList_extend right ext
  · rw [erase];rfl
  · have h : (eraseState out).stack=(eraseState initial).stack := by rw [erase];rfl
    simpa [eraseState,State.map,empty] using h
  · have h : (eraseState out).pc=55 := by rw [erase];rfl
    exact h
  · rw [erase];rfl
  · exact (terminal_accounting run bounded stop).2.trans
      (SupportSearchEncoding.complete_mono 56 H A _ _ (steps_bound xs ys))
end DirectedFlowCutGap.BinaryMaximumProgram
