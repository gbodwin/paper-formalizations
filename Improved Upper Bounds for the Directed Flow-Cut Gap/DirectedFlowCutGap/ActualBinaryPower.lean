import DirectedFlowCutGap.BinaryPowerExecution
import DirectedFlowCutGap.ActualSupportSearch

namespace DirectedFlowCutGap.BinaryPowerProgram
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal
open BooleanTableRead PackedBooleanConstructor

theorem power_bit {H A : ℕ} {word : Bits}
    (initial : BitState 96) (bounded : initial.Bounded H A) (pc0 : initial.pc=94)
    (dense : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (input : BoolList (eraseState initial).heap (eraseState initial).registers.a word) :
    ∃ charge out,Run program (steps word+1) charge initial [] out ∧
      BoolList (eraseState out).heap (eraseState out).registers.d (BinaryCounters.powerOfTwoBinary word).1 ∧
      BoolList (eraseState out).heap (eraseState initial).registers.a word ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=95 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext ∧ ext.length=cells word) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 96 H A (inputSteps word) := by
  have dense' : (eraseState initial).next=(eraseState initial).heap.length := by
    simpa [eraseState,State.map] using dense
  have start : state (eraseState initial).heap (eraseState initial).next
      (eraseState initial).registers.a (eraseState initial).registers.b (eraseState initial).registers.c
      (eraseState initial).registers.d (eraseState initial).stack initial.source 94=eraseState initial := by
    cases initial
    simp_all [eraseState,State.map,state]
  obtain ⟨ext,root,len,high,rep⟩ := power input (eraseState initial).next
    (eraseState initial).registers.b
    (eraseState initial).registers.c (eraseState initial).registers.d
    dense' (eraseState initial).stack initial.source
  rw [start] at high
  have halt : tickNatural program (state ((eraseState initial).heap++ext)
      ((eraseState initial).next+ext.length) (eraseState initial).registers.a
      (eraseState initial).registers.b (eraseState initial).registers.c root
      (eraseState initial).stack initial.source 95)=none := by simp [tickNatural,state,program]
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
  · have h : (eraseState out).pc=95 := by rw [erase];rfl
    exact h
  · rw [erase];rfl
  · exact (terminal_accounting run bounded stop).2.trans
      (SupportSearchEncoding.complete_mono 96 H A _ _ (steps_bound word))
end DirectedFlowCutGap.BinaryPowerProgram
