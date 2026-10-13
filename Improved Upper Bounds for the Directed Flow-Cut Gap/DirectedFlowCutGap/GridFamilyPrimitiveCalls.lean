import DirectedFlowCutGap.GridFamilyCallLift

namespace DirectedFlowCutGap.GridFamily
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead
set_option maxRecDepth 32768

theorem zero_call {heap : NaturalHeap} {a : ℕ} {word : Bits}
    (input : BoolList heap a word) (next b c d : ℕ) (dense : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 10180) (stack : List (Frame ℕ 10180)) (source : Bits) :
    NaturalRun program (BinaryZeroProgram.steps word+2)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 10007) []
      (state (heap++[.flag (isZero word).1]) (next+1) saved.a saved.b saved.c next stack source pc) := by
  have first : tickNatural BinaryZeroProgram.program
      (BinaryZeroProgram.state heap next a b c d [] source 7)=
      some ⟨BinaryZeroProgram.state heap next a b c d [⟨8,.r3,⟨a,b,c,d⟩⟩] source 0,[],0⟩ := by rfl
  have core := NaturalRun.step first
    (BinaryZeroProgram.zero_return input next b c d dense ⟨a,b,c,d⟩ 8 [] source)
  have lift := child_return zeroLabel BinaryZeroProgram.program zero_slots core rfl rfl .r3 .r3
    saved pc stack (by simp only [BinaryZeroProgram.state]; simp [program,zeroLabel,callable,BinaryZeroProgram.program])
  simpa [state,BinaryZeroProgram.state,zeroLabel,Registers.get,Registers.set,Nat.add_assoc] using lift

theorem increment_call {heap : NaturalHeap} {a : ℕ} {word : Bits}
    (input : BoolList heap a word) (next b c d : ℕ) (dense : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 10180) (stack : List (Frame ℕ 10180)) (source : Bits) :
    ∃ ext root,NaturalRun program (BinaryIncrementProgram.steps word+2)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 10024) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      BoolList (heap++ext) root (increment true word).1 := by
  obtain ⟨ext,root,len,run,rep⟩ := BinaryIncrementProgram.increment_return input next b c d dense
    ⟨a,b,c,d⟩ 14 [] source
  have first : tickNatural BinaryIncrementProgram.program
      (BinaryIncrementProgram.state heap next a b c d [] source 15)=
      some ⟨BinaryIncrementProgram.state heap next a b c d [⟨14,.r3,⟨a,b,c,d⟩⟩] source 0,[],0⟩ := by rfl
  have lift := child_return incrementLabel BinaryIncrementProgram.program increment_slots
    (NaturalRun.step first run) rfl rfl .r3 .r3 saved pc stack (by simp only [BinaryIncrementProgram.state]; simp [program,incrementLabel,callable,BinaryIncrementProgram.program])
  refine ⟨ext,root,?_,rep⟩
  simpa [state,BinaryIncrementProgram.state,incrementLabel,Registers.get,Registers.set,len,
    Nat.add_assoc] using lift

theorem predecessor_call {heap : NaturalHeap} {a : ℕ} {word : Bits}
    (input : BoolList heap a word) (next b c d : ℕ) (dense : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 10180) (stack : List (Frame ℕ 10180)) (source : Bits) :
    ∃ ext root,NaturalRun program (BinaryPredecessorProgram.steps word+2)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 10087) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      BoolList (heap++ext) root (predecessor word).1 := by
  obtain ⟨ext,root,_,run,rep⟩ := BinaryPredecessorProgram.pred input next b c d dense [] source
  have lift := child_return predecessorLabel BinaryPredecessorProgram.program predecessor_slots
    run rfl rfl .r3 .r3 saved pc stack (by simp only [BinaryPredecessorProgram.state]; simp [program,predecessorLabel,callable,BinaryPredecessorProgram.program])
  refine ⟨ext,root,?_,rep⟩
  simpa [state,BinaryPredecessorProgram.state,predecessorLabel,Registers.get,Registers.set,Nat.add_assoc] using lift
end DirectedFlowCutGap.GridFamily
