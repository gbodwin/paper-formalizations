import DirectedFlowCutGap.LambdaRowCallLift

set_option maxRecDepth 8192

namespace DirectedFlowCutGap.LambdaRowProgram
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead
open RationalComparisonProgram

theorem read_call {word : Bits} {rows : List Fraction} {heap : NaturalHeap} {a b : ℕ}
    (input : BoolList heap a word) (table : WordPairTableRead.Table heap b (IndexedRationalRead.fields rows))
    (hi : value word<rows.length) (next c d : ℕ) (dense : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 480) (stack : List (Frame ℕ 480)) (source : Bits) :
    ∃ ext root,ext.length=value word+2 ∧
      NaturalRun program (BinaryIndexedPairRead.steps word+4)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 28) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Stored (heap++ext) root (IndexedRationalRead.lookup rows word) := by
  obtain ⟨ext,root,len,core,rep⟩ := IndexedRationalRead.read_high
    (IndexedRationalRead.state heap next a b c d [] source 28) rfl dense rfl input table hi
  have lift := child_return readLabel IndexedRationalRead.program read_slots core rfl rfl
    .r3 .r3 saved pc stack (by rfl)
  exact ⟨ext,root,len,by simpa [IndexedRationalRead.state,readLabel,state,Registers.get,Registers.set,Nat.add_assoc] using lift,rep⟩

theorem core_call {x : Fraction} {dimension exponent : Bits} {heap : NaturalHeap} {a b c : ℕ}
    (cost : Stored heap a x) (dim : BoolList heap b dimension) (exp : BoolList heap c exponent)
    (next d : ℕ) (dense : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 480) (stack : List (Frame ℕ 480)) (source : Bits) :
    ∃ ext root,ext.length=LambdaCoreProgram.cells x dimension exponent ∧
      NaturalRun program (LambdaCoreProgram.steps x dimension exponent+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 460) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Stored (heap++ext) root (LambdaCoreProgram.result x dimension exponent) := by
  obtain ⟨ext,root,len,core,rep⟩ := LambdaCoreProgram.compute cost dim exp next d dense [] source
  have lift := child_return coreLabel LambdaCoreProgram.program core_slots core rfl rfl
    .r3 .r3 saved pc stack (by rfl)
  exact ⟨ext,root,len,by simpa [LambdaCoreProgram.state,coreLabel,state,Registers.get,Registers.set,Nat.add_assoc] using lift,rep⟩
end DirectedFlowCutGap.LambdaRowProgram
