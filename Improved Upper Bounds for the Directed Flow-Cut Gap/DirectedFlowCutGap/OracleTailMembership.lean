import DirectedFlowCutGap.OracleMaskComparison

namespace DirectedFlowCutGap.OracleMask
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor GraphWalkExtension

theorem member_return {heap : NaturalHeap} {a b : ℕ} {es : List (Bits × Bits)} {u : Bits}
    (input : EdgeList heap a es) (query : BoolList heap b u)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 160)
    (stack : List (Frame ℕ 160)) (source : Bits) :
    ∃ ext root,ext.length=memberCells u es ∧ NaturalRun program (memberSteps u es)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 60) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      (heap++ext)[root]?=some (.flag (member u es)) := by
  induction es generalizing heap a b next c d saved pc stack with
  | nil =>
    cases input with
    | nil hp =>
      let frames := (⟨pc,.r3,saved⟩::stack)
      have t60 : tickNatural program (state heap next a b c d frames source 60)=
          some ⟨state heap next a b c d frames source 61,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,hp,tagBranch]
      have t61 : tickNatural program (state heap next a b c d frames source 61)=
          some ⟨state (heap++[.flag false]) (next+1) a b c next frames source 62,[],0⟩ := by
        simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.set]
      have t62 : tickNatural program (state (heap++[.flag false]) (next+1) a b c next frames source 62)=
          some ⟨state (heap++[.flag false]) (next+1) saved.a saved.b saved.c next stack source pc,[],0⟩ := by
        simp [tickNatural,program,state,frames,Registers.get,Registers.set]
      exact ⟨[.flag false],next,rfl,by simpa [memberSteps] using
        (NaturalRun.step t60 (.step t61 (.step t62 (.done _)))),by simp [member,hn]⟩
  | cons e es ih =>
    cases input with
    | @cons _ head tail _ _ hp he ht =>
      obtain ⟨er,et,hep,her,_⟩ := he
      let frames := (⟨pc,.r3,saved⟩::stack)
      obtain ⟨e1,flag,len1,core,htag⟩ := compare_return her query next a d hn
        ⟨er,b,a,d⟩ 67 frames source
      have t60 : tickNatural program (state heap next a b c d frames source 60)=
          some ⟨state heap next a b c d frames source 63,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,hp,tagBranch]
      have t63 : tickNatural program (state heap next a b c d frames source 63)=
          some ⟨state heap next a b a d frames source 64,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set]
      have t64 : tickNatural program (state heap next a b a d frames source 64)=
          some ⟨state heap next head b a d frames source 65,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,hp]
      have t65 : tickNatural program (state heap next head b a d frames source 65)=
          some ⟨state heap next er b a d frames source 66,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,hep]
      have t66 : tickNatural program (state heap next er b a d frames source 66)=
          some ⟨state heap next er b a d (⟨67,.r3,⟨er,b,a,d⟩⟩::frames) source 48,[],0⟩ := by
        simp [tickNatural,program,state]
      have preRun := NaturalRun.step t60 (.step t63 (.step t64 (.step t65 (.step t66 core))))
      have branch : tickNatural program (state (heap++e1) (next+e1.length) er b a flag frames source 67)=
          some ⟨state (heap++e1) (next+e1.length) er b a flag frames source
            (if same e.1 u then 70 else 68),[],0⟩ := by
        cases h : BinaryComparisonProgram.order e.1 u <;>
          simp [tickNatural,program,state,Registers.get,htag,h,tagBranch,same,
            SupportRecoveryProgram.same,BinaryComparisonProgram.tag]
      by_cases h : same e.1 u=true
      · have make : tickNatural program (state (heap++e1) (next+e1.length) er b a flag frames source 70)=
            some ⟨state ((heap++e1)++[.flag true]) (next+e1.length+1) er b a
              (next+e1.length) frames source 71,[],0⟩ := by
          simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.set]
        have ret : tickNatural program (state ((heap++e1)++[.flag true]) (next+e1.length+1)
            er b a (next+e1.length) frames source 71)=
            some ⟨state ((heap++e1)++[.flag true]) (next+e1.length+1)
              saved.a saved.b saved.c (next+e1.length) stack source pc,[],0⟩ := by
          simp [tickNatural,program,state,frames,Registers.get,Registers.set]
        simp only [h,ite_true] at branch
        refine ⟨e1++[.flag true],next+e1.length,by simp [memberCells,h,len1],?_,?_⟩
        · convert run_append preRun (.step branch (.step make (.step ret (.done _)))) using 1 <;>
            simp [memberSteps,h,List.append_assoc,state]
          omega
        · simp [member,h,hn]
      · obtain ⟨e2,root,len2,body,out⟩ := ih (edgeList_extend ht e1) (boolList_extend query e1)
          (next+e1.length) a flag (by simp [hn]) ⟨tail,b,a,flag⟩ 72 frames
        have t68 : tickNatural program (state (heap++e1) (next+e1.length) er b a flag frames source 68)=
            some ⟨state (heap++e1) (next+e1.length) tail b a flag frames source 69,[],0⟩ := by
          simp [tickNatural,program,state,Registers.get,Registers.set,lookup_extend hp e1]
        have t69 : tickNatural program (state (heap++e1) (next+e1.length) tail b a flag frames source 69)=
            some ⟨state (heap++e1) (next+e1.length) tail b a flag
              (⟨72,.r3,⟨tail,b,a,flag⟩⟩::frames) source 60,[],0⟩ := by
          simp [tickNatural,program,state]
        have t72 : tickNatural program
            (state ((heap++e1)++e2) (next+e1.length+e2.length) tail b a root frames source 72)=
            some ⟨state ((heap++e1)++e2) (next+e1.length+e2.length)
              saved.a saved.b saved.c root stack source pc,[],0⟩ := by
          simp [tickNatural,program,state,frames,Registers.get,Registers.set]
        simp only [h] at branch
        refine ⟨e1++e2,root,by simp [memberCells,h,len1,len2],?_,?_⟩
        · convert run_append preRun (.step branch (.step t68 (.step t69
            (run_append body (.step t72 (.done _)))))) using 1 <;>
            simp [memberSteps,h,List.append_assoc,state]
          all_goals omega
        · simpa [member,h,List.append_assoc] using out

end DirectedFlowCutGap.OracleMask
