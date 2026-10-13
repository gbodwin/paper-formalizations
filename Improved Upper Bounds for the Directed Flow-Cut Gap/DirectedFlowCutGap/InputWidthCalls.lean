import DirectedFlowCutGap.InputWidthCallLift

namespace DirectedFlowCutGap.InputWidthProgram
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead

theorem width_call {q : BinaryRational.Fraction} {heap : NaturalHeap} {a : ℕ}
    (input : RationalComparisonProgram.Stored heap a q) (next b c d : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 208) (stack : List (Frame ℕ 208)) (source : Bits) :
    ∃ ext root,ext.length=FractionWidthProgram.cells q ∧
      NaturalRun program (FractionWidthProgram.steps q+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 126) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      BoolList (heap++ext) root (BinaryFractionalGuesses.fractionWidth q).1 := by
  obtain ⟨ext,root,len,core,rep⟩ := FractionWidthProgram.width input next b c d hn [] source
  have lift := child_return widthLabel FractionWidthProgram.program width_slots core rfl rfl
    .r3 .r3 saved pc stack (by rfl)
  exact ⟨ext,root,len,by simpa [FractionWidthProgram.state,widthLabel,state,Registers.get,Registers.set,Nat.add_assoc] using lift,rep⟩

theorem max_call {xs ys : Bits} {heap : NaturalHeap} {a b : ℕ}
    (left : BoolList heap a xs) (right : BoolList heap b ys)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 208)
    (stack : List (Frame ℕ 208)) (source : Bits) :
    ∃ ext root,ext.length=BinaryComparisonProgram.cells xs ys+1 ∧
      NaturalRun program (BinaryMaximumProgram.steps xs ys+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 182) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      BoolList (heap++ext) root (BinaryFractionalGuesses.maximum xs ys).1 := by
  obtain ⟨ext,len,core,rep⟩ := BinaryMaximumProgram.maximum left right next c d hn [] source
  have lift := child_return maxLabel BinaryMaximumProgram.program max_slots core rfl rfl
    .r3 .r3 saved pc stack (by rfl)
  exact ⟨ext,_,len,by simpa [BinaryMaximumProgram.state,maxLabel,state,Registers.get,Registers.set,Nat.add_assoc] using lift,rep⟩
end DirectedFlowCutGap.InputWidthProgram
