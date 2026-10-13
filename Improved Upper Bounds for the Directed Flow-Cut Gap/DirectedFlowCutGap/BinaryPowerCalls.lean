import DirectedFlowCutGap.BinaryPowerCallLift
namespace DirectedFlowCutGap.BinaryPowerProgram
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead

theorem zero_call {word : Bits} {heap : NaturalHeap} {a : ℕ}
    (input : BoolList heap a word) (next b c d : ℕ) (dense : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 96) (stack : List (Frame ℕ 96)) (source : Bits) :
    NaturalRun program (BinaryZeroProgram.steps word+2)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 71) []
      (state (heap++[.flag (isZero word).1]) (next+1) saved.a saved.b saved.c next stack source pc) := by
  have top : tickNatural BinaryZeroProgram.program (BinaryZeroProgram.state heap next a b c d [] source 7)=
      some ⟨BinaryZeroProgram.state heap next a b c d [⟨8,.r3,⟨a,b,c,d⟩⟩] source 0,[],0⟩ := by rfl
  have core := NaturalRun.step top (BinaryZeroProgram.zero_return input next b c d dense ⟨a,b,c,d⟩ 8 [] source)
  have lift := child_return zeroLabel BinaryZeroProgram.program zero_slots core rfl rfl .r3 .r3 saved pc stack (by rfl)
  convert lift using 1 <;> simp [BinaryZeroProgram.state,zeroLabel,state,Registers.get,Registers.set]

theorem pred_call {word : Bits} {heap : NaturalHeap} {a : ℕ}
    (input : BoolList heap a word) (next b c d : ℕ) (dense : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 96) (stack : List (Frame ℕ 96)) (source : Bits) :
    ∃ ext root,ext.length=BinaryPredecessorProgram.cells word ∧
      NaturalRun program (BinaryPredecessorProgram.steps word+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 62) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      BoolList (heap++ext) root (predecessor word).1 := by
  obtain ⟨ext,root,len,core,rep⟩ := BinaryPredecessorProgram.pred input next b c d dense [] source
  have lift := child_return predLabel BinaryPredecessorProgram.program pred_slots core rfl rfl .r3 .r3 saved pc stack (by rfl)
  refine ⟨ext,root,len,?_,rep⟩
  simpa [BinaryPredecessorProgram.state,predLabel,state,Registers.get,Registers.set,Nat.add_assoc] using lift
end DirectedFlowCutGap.BinaryPowerProgram
