import DirectedFlowCutGap.BinaryMaximumCallLift

namespace DirectedFlowCutGap.BinaryMaximumProgram
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor

theorem compare_call {xs ys : Bits} {heap : NaturalHeap} {a b : ℕ}
    (left : BoolList heap a xs) (right : BoolList heap b ys)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 56)
    (stack : List (Frame ℕ 56)) (source : Bits) :
    ∃ ext root,ext.length=BinaryComparisonProgram.cells xs ys+1 ∧
      NaturalRun program (BinaryComparisonProgram.steps xs ys+4)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 30) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      (heap++ext)[root]?=some (.flag (lessEqual xs ys).1) := by
  obtain ⟨out,core,rep,_,_,_,_,_,frames,src,hpc,dense,⟨ext,he,len⟩,_⟩ := BinaryComparisonProgram.compare_high
    (BinaryComparisonProgram.state heap next a b c d [] source 30) rfl hn left right rfl
  have lift := child_return label BinaryComparisonProgram.program slots core rfl frames
    .r3 .r3 saved pc stack (by rw [hpc];rfl)
  have un : out.next=next+ext.length := by rw [dense,he];simp [BinaryComparisonProgram.state,hn]
  refine ⟨ext,out.registers.d,len,?_,?_⟩
  · simpa [BinaryComparisonProgram.state,label,state,Registers.get,Registers.set,he,un,src,Nat.add_assoc] using lift
  · simpa only [he,BinaryComparisonProgram.state] using rep

theorem maximum_return {xs ys : Bits} {heap : NaturalHeap} {a b : ℕ}
    (left : BoolList heap a xs) (right : BoolList heap b ys)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 56)
    (stack : List (Frame ℕ 56)) (source : Bits) :
    ∃ ext,ext.length=BinaryComparisonProgram.cells xs ys+1 ∧
      NaturalRun program (steps xs ys)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 48) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c (pointer xs ys a b) stack source pc) ∧
      BoolList (heap++ext) (pointer xs ys a b) (BinaryFractionalGuesses.maximum xs ys).1 := by
  let frame : Frame ℕ 56 := ⟨pc,.r3,saved⟩
  obtain ⟨ext,root,len,core,rep⟩ := compare_call left right next c d hn ⟨a,b,c,d⟩ 49 (frame::stack) source
  have first : tickNatural program (state heap next a b c d (frame::stack) source 48)=
      some ⟨state heap next a b c d (⟨49,.r3,⟨a,b,c,d⟩⟩::frame::stack) source 30,[],0⟩ := by rfl
  refine ⟨ext,len,?_,?_⟩
  · cases h : (lessEqual xs ys).1 with
    | false =>
      have branch : tickNatural program (state (heap++ext) (next+ext.length) a b c root (frame::stack) source 49)=
          some ⟨state (heap++ext) (next+ext.length) a b c root (frame::stack) source 50,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,rep,h,tagBranch]
      have ret : tickNatural program (state (heap++ext) (next+ext.length) a b c root (frame::stack) source 50)=
          some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c a stack source pc,[],0⟩ := by
        simp [tickNatural,program,state,frame,Registers.get,Registers.set]
      simpa [steps,pointer,h,Nat.add_assoc] using NaturalRun.step first (run_append core (.step branch (.step ret (.done _))))
    | true =>
      have branch : tickNatural program (state (heap++ext) (next+ext.length) a b c root (frame::stack) source 49)=
          some ⟨state (heap++ext) (next+ext.length) a b c root (frame::stack) source 51,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,rep,h,tagBranch]
      have ret : tickNatural program (state (heap++ext) (next+ext.length) a b c root (frame::stack) source 51)=
          some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c b stack source pc,[],0⟩ := by
        simp [tickNatural,program,state,frame,Registers.get,Registers.set]
      simpa [steps,pointer,h,Nat.add_assoc] using NaturalRun.step first (run_append core (.step branch (.step ret (.done _))))
  · cases h : (lessEqual xs ys).1 with
    | false => simpa [pointer,BinaryFractionalGuesses.maximum,h] using boolList_extend left ext
    | true => simpa [pointer,BinaryFractionalGuesses.maximum,h] using boolList_extend right ext
end DirectedFlowCutGap.BinaryMaximumProgram
