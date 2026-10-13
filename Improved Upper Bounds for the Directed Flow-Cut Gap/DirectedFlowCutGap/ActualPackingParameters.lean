import DirectedFlowCutGap.PackingParametersBounds

namespace DirectedFlowCutGap.PackingParameters
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor
open BooleanTableRead (BoolList)
open CanonicalRationalSum (StoredList)
open RationalComparisonProgram (Stored)

/-- Both original parameters are constructed from the actual capacity row in this
same physical run, including the terminal attempt. -/
theorem parameters_bit {H A : ℕ} (row : List Fraction) (initial : BitState 360)
    (bounded : initial.Bounded H A) (pc0 : initial.pc=310)
    (dense : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (input : StoredList (eraseState initial).heap (eraseState initial).registers.a row) :
    ∃ charge out, Run program (steps row.length) charge initial [] out ∧
      (∃ delta fuel, (eraseState out).heap[(eraseState out).registers.d]?=some (.pair delta fuel) ∧
        Stored (eraseState out).heap delta (deltaValue row.length) ∧
        BoolList (eraseState out).heap fuel (fuelWord row.length)) ∧
      StoredList (eraseState out).heap (eraseState initial).registers.a row ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=328 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 360 H A (instructionBound row.length) := by
  have dense' : (eraseState initial).next=(eraseState initial).heap.length := by
    simpa [eraseState,State.map] using dense
  have start : state (eraseState initial).heap (eraseState initial).next
      (eraseState initial).registers.a (eraseState initial).registers.b (eraseState initial).registers.c
      (eraseState initial).registers.d [] initial.source 310=eraseState initial := by
    cases initial
    simp_all [eraseState,State.map,state]
  obtain ⟨ext,highOut,high,heap,next,stack,source,pc,rep⟩ := parameters_run input
    (eraseState initial).next (eraseState initial).registers.b (eraseState initial).registers.c
    (eraseState initial).registers.d dense' initial.source
  rw [start] at high
  have halt : tickNatural program highOut=none := by
    have slot : program 328=.halt := rfl
    simp only [tickNatural,pc,slot]
  obtain ⟨charge,out,run,erase,_,_,sourceOut⟩ := polynomial_simulation bounded high
  have stop : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase,halt] at obs
    cases h : tick program out with
    | none => rfl
    | some r => simp [h] at obs
  refine ⟨charge,out,run,?_,?_,sourceOut.trans source,?_,?_,⟨ext,?_⟩,stop,
    (terminal_accounting run bounded stop).2.trans
      (SupportSearchEncoding.complete_mono 360 H A _ _ (steps_bound row.length))⟩
  · rw [erase];exact rep
  · rw [erase,heap];exact CanonicalRationalSum.list_extend input ext
  · have h : (eraseState out).stack=[] := by rw [erase];exact stack
    simpa [eraseState,State.map] using h
  · have h : (eraseState out).pc=328 := by rw [erase];exact pc
    exact h
  · rw [erase];exact heap
end DirectedFlowCutGap.PackingParameters
