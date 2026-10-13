import DirectedFlowCutGap.BinaryPredecessorCallLift

namespace DirectedFlowCutGap.BinaryPredecessorProgram
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead

theorem zero_call {word : Bits} {heap : NaturalHeap} {a : ℕ}
    (input : BoolList heap a word) (next b c d : ℕ) (dense : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 64) (stack : List (Frame ℕ 64)) (source : Bits) :
    NaturalRun program (BinaryZeroProgram.steps word+2)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 7) []
      (state (heap++[.flag (isZero word).1]) (next+1) saved.a saved.b saved.c next stack source pc) := by
  have top : tickNatural BinaryZeroProgram.program (BinaryZeroProgram.state heap next a b c d [] source 7)=
      some ⟨BinaryZeroProgram.state heap next a b c d [⟨8,.r3,⟨a,b,c,d⟩⟩] source 0,[],0⟩ := by rfl
  have core := NaturalRun.step top (BinaryZeroProgram.zero_return input next b c d dense ⟨a,b,c,d⟩ 8 [] source)
  have lift := child_return zeroLabel BinaryZeroProgram.program zero_slots core rfl rfl .r3 .r3 saved pc stack (by rfl)
  convert lift using 1 <;> simp [BinaryZeroProgram.state,zeroLabel,state,Registers.get,Registers.set]

theorem borrow_call {word : Bits} {heap : NaturalHeap} {a : ℕ}
    (input : BoolList heap a word) (next b c d : ℕ) (dense : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 64) (stack : List (Frame ℕ 64)) (source : Bits) :
    ∃ ext root,ext.length=BinaryBorrowProgram.cells word ∧
      NaturalRun program (BinaryBorrowProgram.steps word+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 24) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      BoolList (heap++ext) root (predCore word).1 := by
  obtain ⟨ext,root,len,run,rep⟩ := BinaryBorrowProgram.borrow_return input next b c d dense ⟨a,b,c,d⟩ 14 [] source
  have top : tickNatural BinaryBorrowProgram.program (BinaryBorrowProgram.state heap next a b c d [] source 15)=
      some ⟨BinaryBorrowProgram.state heap next a b c d [⟨14,.r3,⟨a,b,c,d⟩⟩] source 0,[],0⟩ := by rfl
  have lift := child_return borrowLabel BinaryBorrowProgram.program borrow_slots (.step top run) rfl rfl .r3 .r3 saved pc stack (by rfl)
  refine ⟨ext,root,len,?_,rep⟩
  convert lift using 1 <;> simp [BinaryBorrowProgram.state,borrowLabel,state,len,Registers.get,Registers.set]

theorem trim_call {word : Bits} {heap : NaturalHeap} {a : ℕ}
    (input : BoolList heap a word) (next b c d : ℕ) (dense : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 64) (stack : List (Frame ℕ 64)) (source : Bits) :
    ∃ ext root,ext.length=(trim word).1.length ∧
      NaturalRun program (BinaryTrimProgram.steps word+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 36) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      BoolList (heap++ext) root (trim word).1 := by
  obtain ⟨ext,root,len,core,rep⟩ := BinaryTrimProgram.trim_high
    (BinaryTrimProgram.state heap next a b c d [] source 11) rfl dense input rfl
  have lift := child_return trimLabel BinaryTrimProgram.program trim_slots core rfl rfl .r3 .r3 saved pc stack (by rfl)
  refine ⟨ext,root,len,?_,rep⟩
  convert lift using 1 <;> simp [BinaryTrimProgram.state,trimLabel,state,Registers.get,Registers.set];omega
end DirectedFlowCutGap.BinaryPredecessorProgram
