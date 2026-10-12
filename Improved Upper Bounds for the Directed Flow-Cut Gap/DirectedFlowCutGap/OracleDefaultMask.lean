import DirectedFlowCutGap.OracleChoiceCalls

namespace DirectedFlowCutGap.OracleChoice
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor

theorem false_mask_return {heap : NaturalHeap} {a : ℕ} {vs : List Bits}
    (input : GraphDiscoveryProgram.Vertices heap a vs) (next b c d : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 484) (stack : List (Frame ℕ 484)) (source : Bits) :
    ∃ ext root,ext.length=2*vs.length+1 ∧ NaturalRun program (6*vs.length+3)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 470) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      BoolList (heap++ext) root (List.replicate vs.length false) := by
  induction input generalizing next b c d saved pc stack with
  | @nil a ha =>
    let frames := (⟨pc,.r3,saved⟩::stack)
    have t470 : tickNatural program (state heap next a b c d frames source 470)=
        some ⟨state heap next a b c d frames source 471,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,tagBranch,ha]
    have t471 : tickNatural program (state heap next a b c d frames source 471)=
        some ⟨state (heap++[.nil]) (next+1) a b c next frames source 472,[],0⟩ := by
      simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.set]
    have t472 : tickNatural program (state (heap++[.nil]) (next+1) a b c next frames source 472)=
        some ⟨state (heap++[.nil]) (next+1) saved.a saved.b saved.c next stack source pc,[],0⟩ := by
      simp [tickNatural,program,state,frames,Registers.get,Registers.set]
    exact ⟨[.nil],next,rfl,.step t470 (.step t471 (.step t472 (.done _))),.nil (by simp [hn])⟩
  | @cons a head tail u us ha hu ht ih =>
    let frames := (⟨pc,.r3,saved⟩::stack)
    obtain ⟨et,rt,lt,body,rep⟩ := ih next b c d hn ⟨tail,b,c,d⟩ 475 frames
    let n1 := next+et.length
    have t470 : tickNatural program (state heap next a b c d frames source 470)=
        some ⟨state heap next a b c d frames source 473,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,tagBranch,ha]
    have t473 : tickNatural program (state heap next a b c d frames source 473)=
        some ⟨state heap next tail b c d frames source 474,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,ha]
    have t474 : tickNatural program (state heap next tail b c d frames source 474)=
        some ⟨state heap next tail b c d (⟨475,.r3,⟨tail,b,c,d⟩⟩::frames) source 470,[],0⟩ := by
      simp [tickNatural,program,state]
    have t475 : tickNatural program (state (heap++et) n1 tail b c rt frames source 475)=
        some ⟨state ((heap++et)++[.flag false]) (n1+1) n1 b c rt frames source 476,[],0⟩ := by
      simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.set]
    have t476 : tickNatural program (state ((heap++et)++[.flag false]) (n1+1) n1 b c rt frames source 476)=
        some ⟨state (((heap++et)++[.flag false])++[.pair n1 rt]) (n1+1+1) n1 b c (n1+1) frames source 477,[],0⟩ := by
      simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.get,Registers.set]
    have t477 : tickNatural program
        (state (((heap++et)++[.flag false])++[.pair n1 rt]) (n1+1+1) n1 b c (n1+1) frames source 477)=
        some ⟨state (((heap++et)++[.flag false])++[.pair n1 rt]) (n1+1+1)
          saved.a saved.b saved.c (n1+1) stack source pc,[],0⟩ := by
      simp [tickNatural,program,state,frames,Registers.get,Registers.set]
    let ext : NaturalHeap := et++[.flag false,.pair n1 rt]
    refine ⟨ext,n1+1,by simp [ext,lt];omega,?_,?_⟩
    · have all := NaturalRun.step t470 (.step t473 (.step t474
        (run_append body (.step t475 (.step t476 (.step t477 (.done _)))))))
      convert all using 1 <;> simp [ext,n1,state,List.append_assoc,List.length_cons]
      all_goals omega
    · simp only [List.length_cons,List.replicate_succ]
      apply BoolList.cons (head:=n1) (tail:=rt)
      · have dense : n1=(heap++et).length := by simp [n1,hn]
        dsimp only [ext]
        rw [←List.append_assoc]
        rw [List.getElem?_append_right (show (heap++et).length≤n1+1 by omega)]
        simp only [←dense,Nat.add_sub_cancel_left]
        rfl
      · have dense : n1=(heap++et).length := by simp [n1,hn]
        dsimp only [ext]
        rw [←List.append_assoc]
        rw [List.getElem?_append_right (show (heap++et).length≤n1 by omega)]
        simp only [←dense,Nat.sub_self]
        rfl
      · simpa [ext,List.append_assoc] using boolList_extend rep [.flag false,.pair n1 rt]

end DirectedFlowCutGap.OracleChoice
