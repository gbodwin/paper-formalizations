import DirectedFlowCutGap.BinaryPowerFinish
namespace DirectedFlowCutGap.BinaryPowerProgram
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor

set_option maxRecDepth 10000 in
theorem power_return {word : Bits} {heap : NaturalHeap} {a : ℕ}
    (input : BoolList heap a word) (next b c d : ℕ) (dense : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 96) (stack : List (Frame ℕ 96)) (source : Bits) :
    ∃ ext root,ext.length=cells word ∧
      NaturalRun program (steps word)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 76) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      BoolList (heap++ext) root (BinaryCounters.powerOfTwoBinary word).1 := by
  induction word using steps.induct generalizing heap a next b c d saved pc stack with
  | case1 word hz =>
    let frame : Frame ℕ 96 := ⟨pc,.r3,saved⟩
    have t76 : tickNatural program (state heap next a b c d (frame::stack) source 76)=
        some ⟨state heap next a b c d (⟨77,.r3,⟨a,b,c,d⟩⟩::frame::stack) source 71,[],0⟩ := by rfl
    have zrun := zero_call input next b c d dense ⟨a,b,c,d⟩ 77 (frame::stack) source
    simp only [hz] at zrun
    have t77 : tickNatural program (state (heap++[.flag true]) (next+1) a b c next (frame::stack) source 77)=
        some ⟨state (heap++[.flag true]) (next+1) a b c next (frame::stack) source 78,[],0⟩ := by
      simp [program,tickNatural,state,dense,Registers.get,tagBranch]
    obtain ⟨finish,rep⟩ := one_return (heap++[.flag true]) (next+1) a b c next (by simp [dense]) saved pc stack source
    have hs : steps word=BinaryZeroProgram.steps word+8 := by rw [steps];simp [hz]
    have hc : cells word=4 := by rw [cells];simp [hz]
    have hw : (BinaryCounters.powerOfTwoBinary word).1=[true] := by
      rw [BinaryCounters.powerOfTwoBinary];simp [hz]
    refine ⟨[.flag true,.flag true,.nil,.pair (next+1) (next+2)],next+3,by simp [hc],?_,?_⟩
    · have all := NaturalRun.step t76 (run_append zrun (.step t77 finish))
      convert all using 1 <;> simp [state,List.append_assoc,Nat.add_assoc]
    · simpa [hw,List.append_assoc,Nat.add_assoc] using rep
  | case2 word hz ih =>
    have hz' : (isZero word).1=false := by cases h : (isZero word).1 <;> simp_all
    let frame : Frame ℕ 96 := ⟨pc,.r3,saved⟩
    let ez : NaturalHeap := [.flag false]
    have t76 : tickNatural program (state heap next a b c d (frame::stack) source 76)=
        some ⟨state heap next a b c d (⟨77,.r3,⟨a,b,c,d⟩⟩::frame::stack) source 71,[],0⟩ := by rfl
    have zrun := zero_call input next b c d dense ⟨a,b,c,d⟩ 77 (frame::stack) source
    simp only [hz'] at zrun
    obtain ⟨ep,pr,plen,prun,prep⟩ := pred_call (boolList_extend input ez)
      (next+1) b c next (by simp [dense,ez]) ⟨a,b,c,next⟩ 82 (frame::stack) source
    obtain ⟨er,rr,rlen,rrun,rrep⟩ := ih prep (next+1+ep.length) b c pr
      (by simp [dense,ez,Nat.add_assoc];omega) ⟨pr,b,c,pr⟩ 84 (frame::stack)
    let H := ((heap++ez)++ep)++er
    let N := next+1+ep.length+er.length
    have nd : N=H.length := by simp [N,H,dense,ez,Nat.add_assoc];omega
    obtain ⟨finish,rep⟩ := shift_return rrep N pr b c nd saved pc stack source
    have t77 : tickNatural program (state (heap++ez) (next+1) a b c next (frame::stack) source 77)=
        some ⟨state (heap++ez) (next+1) a b c next (frame::stack) source 81,[],0⟩ := by
      simp [program,tickNatural,state,ez,dense,Registers.get,tagBranch]
    have t81 : tickNatural program (state (heap++ez) (next+1) a b c next (frame::stack) source 81)=
        some ⟨state (heap++ez) (next+1) a b c next (⟨82,.r3,⟨a,b,c,next⟩⟩::frame::stack) source 62,[],0⟩ := by rfl
    have t82 : tickNatural program (state ((heap++ez)++ep) (next+1+ep.length) a b c pr (frame::stack) source 82)=
        some ⟨state ((heap++ez)++ep) (next+1+ep.length) pr b c pr (frame::stack) source 83,[],0⟩ := by rfl
    have t83 : tickNatural program (state ((heap++ez)++ep) (next+1+ep.length) pr b c pr (frame::stack) source 83)=
        some ⟨state ((heap++ez)++ep) (next+1+ep.length) pr b c pr (⟨84,.r3,⟨pr,b,c,pr⟩⟩::frame::stack) source 76,[],0⟩ := by rfl
    have hs : steps word=BinaryZeroProgram.steps word+BinaryPredecessorProgram.steps word+steps (predecessor word).1+12 := by
      rw [steps];simp [hz]
    have hc : cells word=BinaryPredecessorProgram.cells word+cells (predecessor word).1+3 := by
      rw [cells];simp [hz]
    have hw : (BinaryCounters.powerOfTwoBinary word).1=false::(BinaryCounters.powerOfTwoBinary (predecessor word).1).1 := by
      rw [BinaryCounters.powerOfTwoBinary];simp [hz]
    refine ⟨ez++ep++er++[.flag false,.pair N rr],N+1,?_,?_,?_⟩
    · simp [hc,ez,plen,rlen];omega
    · have all := NaturalRun.step t76 (run_append zrun (.step t77 (.step t81
        (run_append prun (.step t82 (.step t83 (run_append rrun finish)))))))
      convert all using 1 <;> simp [hs,state,ez,N,List.append_assoc,Nat.add_assoc]
      all_goals omega
    · simpa [hw,List.append_assoc] using rep
end DirectedFlowCutGap.BinaryPowerProgram
