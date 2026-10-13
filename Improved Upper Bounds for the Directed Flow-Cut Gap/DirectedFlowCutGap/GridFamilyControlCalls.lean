import DirectedFlowCutGap.GridFamilyPrimitiveCalls

namespace DirectedFlowCutGap.GridFamily
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead
set_option maxRecDepth 32768

theorem zero_helper {heap : NaturalHeap} {c : ℕ} {word : Bits}
    (input : BoolList heap c word) (next a b d : ℕ) (dense : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 10180) (stack : List (Frame ℕ 10180)) (source : Bits) :
    NaturalRun program (BinaryZeroProgram.steps word+5)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 10100) []
      (state (heap++[.flag (isZero word).1]) (next+1) saved.a saved.b saved.c next stack source pc) := by
  let frame : Frame ℕ 10180 := ⟨pc,.r3,saved⟩
  have t0 : tickNatural program (state heap next a b c d (frame::stack) source 10100)=
      some ⟨state heap next c b c d (frame::stack) source 10101,[],0⟩ := by rfl
  have t1 : tickNatural program (state heap next c b c d (frame::stack) source 10101)=
      some ⟨state heap next c b c d (⟨10102,.r3,⟨c,b,c,d⟩⟩::frame::stack) source 10007,[],0⟩ := by rfl
  have run := zero_call input next b c d dense ⟨c,b,c,d⟩ 10102 (frame::stack) source
  have ret : tickNatural program (state (heap++[.flag (isZero word).1]) (next+1) c b c next
      (frame::stack) source 10102)=
      some ⟨state (heap++[.flag (isZero word).1]) (next+1) saved.a saved.b saved.c next stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,frame,Registers.get,Registers.set]
  simpa [frame,Nat.add_assoc] using NaturalRun.step t0 (.step t1 (run_append run (.step ret (.done _))))

theorem increment_helper {heap : NaturalHeap} {b : ℕ} {word : Bits}
    (input : BoolList heap b word) (next a c d : ℕ) (dense : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 10180) (stack : List (Frame ℕ 10180)) (source : Bits) :
    ∃ ext root,NaturalRun program (BinaryIncrementProgram.steps word+5)
      (state heap next a b c d (⟨pc,.r1,saved⟩::stack) source 10104) []
      (state (heap++ext) (next+ext.length) saved.a root saved.c saved.d stack source pc) ∧
      BoolList (heap++ext) root (increment true word).1 := by
  let frame : Frame ℕ 10180 := ⟨pc,.r1,saved⟩
  have t0 : tickNatural program (state heap next a b c d (frame::stack) source 10104)=
      some ⟨state heap next b b c d (frame::stack) source 10105,[],0⟩ := by rfl
  have t1 : tickNatural program (state heap next b b c d (frame::stack) source 10105)=
      some ⟨state heap next b b c d (⟨10106,.r3,⟨b,b,c,d⟩⟩::frame::stack) source 10024,[],0⟩ := by rfl
  obtain ⟨ext,root,run,rep⟩ := increment_call input next b c d dense ⟨b,b,c,d⟩ 10106 (frame::stack) source
  have ret : tickNatural program (state (heap++ext) (next+ext.length) b b c root (frame::stack) source 10106)=
      some ⟨state (heap++ext) (next+ext.length) saved.a root saved.c saved.d stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,frame,Registers.get,Registers.set]
  refine ⟨ext,root,?_,rep⟩
  simpa [frame,Nat.add_assoc] using NaturalRun.step t0 (.step t1 (run_append run (.step ret (.done _))))

theorem predecessor_helper {heap : NaturalHeap} {c : ℕ} {word : Bits}
    (input : BoolList heap c word) (next a b d : ℕ) (dense : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 10180) (stack : List (Frame ℕ 10180)) (source : Bits) :
    ∃ ext root,NaturalRun program (BinaryPredecessorProgram.steps word+5)
      (state heap next a b c d (⟨pc,.r2,saved⟩::stack) source 10107) []
      (state (heap++ext) (next+ext.length) saved.a saved.b root saved.d stack source pc) ∧
      BoolList (heap++ext) root (predecessor word).1 := by
  let frame : Frame ℕ 10180 := ⟨pc,.r2,saved⟩
  have t0 : tickNatural program (state heap next a b c d (frame::stack) source 10107)=
      some ⟨state heap next c b c d (frame::stack) source 10108,[],0⟩ := by rfl
  have t1 : tickNatural program (state heap next c b c d (frame::stack) source 10108)=
      some ⟨state heap next c b c d (⟨10109,.r3,⟨c,b,c,d⟩⟩::frame::stack) source 10087,[],0⟩ := by rfl
  obtain ⟨ext,root,run,rep⟩ := predecessor_call input next b c d dense ⟨c,b,c,d⟩ 10109 (frame::stack) source
  have ret : tickNatural program (state (heap++ext) (next+ext.length) c b c root (frame::stack) source 10109)=
      some ⟨state (heap++ext) (next+ext.length) saved.a saved.b root saved.d stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,frame,Registers.get,Registers.set]
  refine ⟨ext,root,?_,rep⟩
  simpa [frame,Nat.add_assoc] using NaturalRun.step t0 (.step t1 (run_append run (.step ret (.done _))))
end DirectedFlowCutGap.GridFamily
