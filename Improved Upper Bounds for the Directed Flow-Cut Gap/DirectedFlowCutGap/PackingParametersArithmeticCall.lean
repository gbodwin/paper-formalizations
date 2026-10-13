import DirectedFlowCutGap.PackingParametersDimensionCall

namespace DirectedFlowCutGap.PackingParameters
open BinaryArithmetic ImmutableReferenceSimulation PackedBooleanConstructor
open BooleanTableRead (BoolList)

theorem arithmetic_return {xs ys : Bits} {heap : NaturalHeap} {a b : ℕ}
    (left : BoolList heap a xs) (right : BoolList heap b ys) (next c d : ℕ) (dense : next=heap.length)
    (destination : Reg) (saved : Registers ℕ) (pc : Fin 360) (stack : List (Frame ℕ 360)) (source : Bits) :
    ∃ ext root,
      NaturalRun program (CanonicalArithmeticProgram.instructions true xs ys+1)
        (state heap next a b c d (⟨pc,destination,saved⟩::stack) source 134) []
        ⟨heap++ext,next+ext.length,saved.set destination root,stack,pc,source⟩ ∧
      BoolList (heap++ext) root (mulCanonical xs ys).1 := by
  obtain ⟨ext,root,_,run,rep⟩ := CanonicalArithmeticProgram.canonical_high true
    (CanonicalArithmeticProgram.state heap next a b c d [] source 110) rfl dense left right rfl
  have terminal : CanonicalArithmeticProgram.program 115=.halt := rfl
  have lifted := child_return arithmeticLabel CanonicalArithmeticProgram.program arithmetic_slots run rfl rfl
    .r3 destination saved pc stack (arithmetic_halt 115 terminal)
  have entry : arithmeticLabel 110=(134 : Fin 360) := by decide
  exact ⟨ext,root,by simpa only [CanonicalArithmeticProgram.state,entry,state,Registers.get] using lifted,
    by simpa only [CanonicalArithmeticProgram.result_exact,ite_true,CanonicalArithmeticProgram.state] using rep⟩
end DirectedFlowCutGap.PackingParameters
