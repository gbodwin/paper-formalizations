import DirectedFlowCutGap.BinaryPredecessorCalls
namespace DirectedFlowCutGap.BinaryPredecessorProgram
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor

set_option maxRecDepth 10000 in
theorem predecessor_return {word : Bits} {heap : NaturalHeap} {a : ℕ}
    (input : BoolList heap a word) (next b c d : ℕ) (dense : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 64) (stack : List (Frame ℕ 64)) (source : Bits) :
    ∃ ext root,ext.length=cells word ∧
      NaturalRun program (steps word)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 40) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      BoolList (heap++ext) root (predecessor word).1 := by
  let frame : Frame ℕ 64 := ⟨pc,.r3,saved⟩
  have t40 : tickNatural program (state heap next a b c d (frame::stack) source 40)=
      some ⟨state heap next a b c d (⟨41,.r3,⟨a,b,c,d⟩⟩::frame::stack) source 7,[],0⟩ := by rfl
  have zrun := zero_call input next b c d dense ⟨a,b,c,d⟩ 41 (frame::stack) source
  cases hz : (isZero word).1 with
  | true =>
    simp only [hz] at zrun
    let ext : NaturalHeap := [.flag true,.nil]
    have t41 : tickNatural program (state (heap++[.flag true]) (next+1) a b c next (frame::stack) source 41)=
        some ⟨state (heap++[.flag true]) (next+1) a b c next (frame::stack) source 42,[],0⟩ := by
      simp [program,tickNatural,state,dense,Registers.get,tagBranch]
    have t42 : tickNatural program (state (heap++[.flag true]) (next+1) a b c next (frame::stack) source 42)=
        some ⟨state (heap++ext) (next+2) a b c (next+1) (frame::stack) source 43,[],0⟩ := by
      simp [program,tickNatural,state,ext,allocateNatural,Recipe.cell,Registers.set,List.append_assoc,Nat.add_assoc]
    have t43 : tickNatural program (state (heap++ext) (next+2) a b c (next+1) (frame::stack) source 43)=
        some ⟨state (heap++ext) (next+2) saved.a saved.b saved.c (next+1) stack source pc,[],0⟩ := by
      simp [program,tickNatural,state,frame,Registers.get,Registers.set]
    refine ⟨ext,next+1,by simp [cells,hz,ext],?_,?_⟩
    · have all := NaturalRun.step t40 (run_append zrun (.step t41 (.step t42 (.step t43 (.done _)))))
      convert all using 1 <;> simp [steps,hz,Nat.add_assoc]
    · simpa [predecessor,hz] using (show BoolList (heap++ext) (next+1) [] from .nil (by simp [ext,dense]))
  | false =>
    simp only [hz] at zrun
    let ez : NaturalHeap := [.flag false]
    obtain ⟨eb,br,blen,brun,brep⟩ := borrow_call (boolList_extend input ez)
      (next+1) b c next (by simp [dense,ez]) ⟨a,b,c,next⟩ 45 (frame::stack) source
    obtain ⟨et,tr,tlen,trun,trep⟩ := trim_call brep
      (next+1+eb.length) b c br (by simp [dense,ez,Nat.add_assoc];omega)
      ⟨br,b,c,br⟩ 47 (frame::stack) source
    have t41 : tickNatural program (state (heap++ez) (next+1) a b c next (frame::stack) source 41)=
        some ⟨state (heap++ez) (next+1) a b c next (frame::stack) source 44,[],0⟩ := by
      simp [program,tickNatural,state,ez,dense,Registers.get,tagBranch]
    have t44 : tickNatural program (state (heap++ez) (next+1) a b c next (frame::stack) source 44)=
        some ⟨state (heap++ez) (next+1) a b c next (⟨45,.r3,⟨a,b,c,next⟩⟩::frame::stack) source 24,[],0⟩ := by rfl
    have t45 : tickNatural program (state ((heap++ez)++eb) (next+1+eb.length) a b c br (frame::stack) source 45)=
        some ⟨state ((heap++ez)++eb) (next+1+eb.length) br b c br (frame::stack) source 46,[],0⟩ := by rfl
    have t46 : tickNatural program (state ((heap++ez)++eb) (next+1+eb.length) br b c br (frame::stack) source 46)=
        some ⟨state ((heap++ez)++eb) (next+1+eb.length) br b c br (⟨47,.r3,⟨br,b,c,br⟩⟩::frame::stack) source 36,[],0⟩ := by rfl
    have t47 : tickNatural program (state (((heap++ez)++eb)++et) (next+1+eb.length+et.length) br b c tr (frame::stack) source 47)=
        some ⟨state (((heap++ez)++eb)++et) (next+1+eb.length+et.length) saved.a saved.b saved.c tr stack source pc,[],0⟩ := by
      simp [program,tickNatural,state,frame,Registers.get,Registers.set]
    refine ⟨ez++eb++et,tr,?_,?_,?_⟩
    · simp [cells,hz,ez,blen,tlen,Nat.add_comm,Nat.add_left_comm]
    · have all := NaturalRun.step t40 (run_append zrun (.step t41 (.step t44
        (run_append brun (.step t45 (.step t46 (run_append trun (.step t47 (.done _)))))))))
      convert all using 1 <;> simp [steps,hz,state,ez,List.append_assoc,Nat.add_assoc]
      all_goals omega
    · simpa [predecessor,hz,List.append_assoc] using trep
end DirectedFlowCutGap.BinaryPredecessorProgram
