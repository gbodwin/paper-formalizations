import DirectedFlowCutGap.BinarySizeCallLift

namespace DirectedFlowCutGap.BinarySizeProgram
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead

theorem trim_call {word : Bits} {heap : NaturalHeap} {a : ℕ}
    (input : BoolList heap a word) (next b c d : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 48) (stack : List (Frame ℕ 48)) (source : Bits) :
    ∃ ext root,ext.length=(trim word).1.length ∧
      NaturalRun program (BinaryTrimProgram.steps word+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 11) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      BoolList (heap++ext) root (trim word).1 := by
  obtain ⟨ext,root,len,core,rep⟩ := BinaryTrimProgram.trim_high
    (BinaryTrimProgram.state heap next a b c d [] source 11) rfl hn input rfl
  have lift := child_return trimLabel BinaryTrimProgram.program trim_slots core rfl rfl
    .r3 .r3 saved pc stack (by rfl)
  rw [show (1+BinaryTrimProgram.steps word)+1=BinaryTrimProgram.steps word+2 by omega] at lift
  exact ⟨ext,root,len,by simpa [BinaryTrimProgram.state,trimLabel,state,Registers.get,Registers.set] using lift,rep⟩

theorem length_call {word : Bits} {heap : NaturalHeap} {a : ℕ}
    (input : BoolList heap a word) (next b c d : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 48) (stack : List (Frame ℕ 48)) (source : Bits) :
    ∃ ext root,ext.length=1+BinaryLengthProgram.scanCells word.length [] ∧
      NaturalRun program (BinaryLengthProgram.scanSteps word.length []+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 29) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      BoolList (heap++ext) root (BinaryCounters.lengthBits word).1 := by
  obtain ⟨out,core,rep,_,_,⟨ext,he,len⟩,dense,frames,src,hpc,_⟩ := BinaryLengthProgram.length_high
    (BinaryLengthProgram.state heap next a b c d source 16) rfl hn input rfl
  have lift := child_return lengthLabel BinaryLengthProgram.program length_slots core rfl frames
    .r1 .r3 saved pc stack (by rw [hpc];rfl)
  rw [show (1+BinaryLengthProgram.scanSteps word.length [])+1=BinaryLengthProgram.scanSteps word.length []+2 by omega] at lift
  have un : out.next=next+ext.length := by rw [dense,he];simp [BinaryLengthProgram.state,hn]
  refine ⟨ext,out.registers.b,len,?_,?_⟩
  · simpa [BinaryLengthProgram.state,lengthLabel,state,Registers.get,Registers.set,he,un,src] using lift
  · simpa only [he,BinaryLengthProgram.state,countWord_exact] using rep
end DirectedFlowCutGap.BinarySizeProgram
