import DirectedFlowCutGap.PackingCompleteCallLift

namespace DirectedFlowCutGap.PackingComplete
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation
open BooleanTableRead (BoolList)
open CanonicalRationalSum (StoredList)
open RationalComparisonProgram (Stored)

theorem parameters_return {row : List Fraction} {heap : NaturalHeap} {cap : ℕ}
    (input : StoredList heap cap row) (next b c d : ℕ) (dense : next=heap.length)
    (source : Bits) (saved : Registers ℕ) (pc : Fin 8340) (stack : List (Frame ℕ 8340)) :
    ∃ ext root delta fuel,
      NaturalRun program (PackingParameters.steps row.length+1)
        (state heap next cap b c d (⟨pc,.r2,saved⟩::stack) source 310) []
        (state (heap++ext) (next+ext.length) saved.a saved.b root saved.d stack source pc) ∧
      (heap++ext)[root]?=some (.pair delta fuel) ∧
      Stored (heap++ext) delta (PackingParameters.deltaValue row.length) ∧
      BoolList (heap++ext) fuel (PackingParameters.fuelWord row.length) := by
  obtain ⟨ext,out,run,he,nd,st,src,outpc,delta,fuel,pair,deltaRep,fuelRep⟩ :=
    PackingParameters.parameters_run input next b c d dense source
  have terminal : PackingParameters.program out.pc=.halt := by rw [outpc];rfl
  have lifted := child_return parameterLabel PackingParameters.program parameter_slots run rfl st
    .r3 .r2 saved pc stack (parameter_halt out.pc terminal)
  have entry : parameterLabel 310=(310 : Fin 8340) := rfl
  refine ⟨ext,out.registers.d,delta,fuel,?_,?_,?_,?_⟩
  · simpa only [PackingParameters.state,entry,state,he,nd,src,Registers.set,Registers.get] using lifted
  · simpa only [he] using pair
  · simpa only [he] using deltaRep
  · simpa only [he] using fuelRep
end DirectedFlowCutGap.PackingComplete
