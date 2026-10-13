import DirectedFlowCutGap.FractionWidthCallLift

namespace DirectedFlowCutGap.FractionWidthProgram
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead

theorem size_call {word : Bits} {heap : NaturalHeap} {a : ℕ}
    (input : BoolList heap a word) (next b c d : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 128) (stack : List (Frame ℕ 128)) (source : Bits) :
    ∃ ext root,ext.length=BinarySizeProgram.cells word ∧
      NaturalRun program (BinarySizeProgram.steps word+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 46) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      BoolList (heap++ext) root (BinaryCounters.sizeBits word).1 := by
  obtain ⟨ext,root,len,core,rep⟩ := BinarySizeProgram.size input next b c d hn [] source
  have lift := child_return sizeLabel BinarySizeProgram.program size_slots core rfl rfl
    .r3 .r3 saved pc stack (by rfl)
  exact ⟨ext,root,len,by simpa [BinarySizeProgram.state,sizeLabel,state,Registers.get,Registers.set,Nat.add_assoc] using lift,rep⟩

theorem max_call {xs ys : Bits} {heap : NaturalHeap} {a b : ℕ}
    (left : BoolList heap a xs) (right : BoolList heap b ys)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 128)
    (stack : List (Frame ℕ 128)) (source : Bits) :
    ∃ ext root,ext.length=BinaryComparisonProgram.cells xs ys+1 ∧
      NaturalRun program (BinaryMaximumProgram.steps xs ys+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 102) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      BoolList (heap++ext) root (BinaryFractionalGuesses.maximum xs ys).1 := by
  obtain ⟨ext,len,core,rep⟩ := BinaryMaximumProgram.maximum left right next c d hn [] source
  have lift := child_return maxLabel BinaryMaximumProgram.program max_slots core rfl rfl
    .r3 .r3 saved pc stack (by rfl)
  exact ⟨ext,_,len,by simpa [BinaryMaximumProgram.state,maxLabel,state,Registers.get,Registers.set,Nat.add_assoc] using lift,rep⟩
end DirectedFlowCutGap.FractionWidthProgram
