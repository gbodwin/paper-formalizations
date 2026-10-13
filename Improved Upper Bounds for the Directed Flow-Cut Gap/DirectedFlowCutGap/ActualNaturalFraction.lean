import DirectedFlowCutGap.NaturalFractionExecution
import DirectedFlowCutGap.ActualSupportSearch

namespace DirectedFlowCutGap.NaturalFractionProgram
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal
open BooleanTableRead PackedBooleanConstructor

theorem fraction_bit {H A : ℕ} {word : Bits}
    (initial : BitState 8) (bounded : initial.Bounded H A) (pc0 : initial.pc=6)
    (dense : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (input : BoolList (eraseState initial).heap (eraseState initial).registers.a word) :
    ∃ charge out,Run program 6 charge initial [] out ∧
      RationalComparisonProgram.Stored (eraseState out).heap (eraseState out).registers.d (BinaryFractionalCore.naturalFraction word) ∧
      BoolList (eraseState out).heap (eraseState initial).registers.a word ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=7 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext ∧ ext.length=4) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 8 H A 6 := by
  have dense' : (eraseState initial).next=(eraseState initial).heap.length := by
    simpa [eraseState,State.map] using dense
  have start : state (eraseState initial).heap (eraseState initial).next
      (eraseState initial).registers.a (eraseState initial).registers.b (eraseState initial).registers.c
      (eraseState initial).registers.d (eraseState initial).stack initial.source 6=eraseState initial := by
    cases initial
    simp_all [eraseState,State.map,state]
  obtain ⟨ext,root,len,high,rep⟩ := fraction input (eraseState initial).next
    (eraseState initial).registers.b
    (eraseState initial).registers.c (eraseState initial).registers.d
    dense' (eraseState initial).stack initial.source
  rw [start] at high
  have halt : tickNatural program (state ((eraseState initial).heap++ext)
      ((eraseState initial).next+ext.length) (eraseState initial).registers.a
      (eraseState initial).registers.b (eraseState initial).registers.c root
      (eraseState initial).stack initial.source 7)=none := by simp [tickNatural,state,program]
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
  · rw [erase];exact boolList_extend input ext
  · have h : (eraseState out).stack=(eraseState initial).stack := by rw [erase];rfl
    simpa [eraseState,State.map,empty] using h
  · have h : (eraseState out).pc=7 := by rw [erase];rfl
    exact h
  · rw [erase];rfl
  · exact (terminal_accounting run bounded stop).2
end DirectedFlowCutGap.NaturalFractionProgram
