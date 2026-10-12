import DirectedFlowCutGap.SupportEdgeComparison

namespace DirectedFlowCutGap.SupportRecoveryProgram
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor GraphWalkExtension

theorem member_return {heap : NaturalHeap} {a b : ℕ} {es : List (Bits × Bits)} {e : Bits × Bits}
    (input : EdgeList heap a es) (query : Edge heap b e)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 280)
    (stack : List (Frame ℕ 280)) (source : Bits) :
    ∃ ext root,ext.length=memberCells e es ∧ NaturalRun program (memberSteps e es)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 90) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      (heap++ext)[root]?=some (.flag (member e es)) := by
  induction es generalizing heap a b next c d saved pc stack with
  | nil =>
    cases input with
    | nil hp =>
      let frames := (⟨pc,.r3,saved⟩::stack)
      have t90 : tickNatural program (state heap next a b c d frames source 90)=
          some ⟨state heap next a b c d frames source 91,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,hp,tagBranch]
      have t91 : tickNatural program (state heap next a b c d frames source 91)=
          some ⟨state (heap++[.flag false]) (next+1) a b c next frames source 92,[],0⟩ := by
        simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.set]
      have t92 : tickNatural program (state (heap++[.flag false]) (next+1) a b c next frames source 92)=
          some ⟨state (heap++[.flag false]) (next+1) saved.a saved.b saved.c next stack source pc,[],0⟩ := by
        simp [tickNatural,program,state,frames,Registers.get,Registers.set]
      exact ⟨[.flag false],next,rfl,by simpa [memberSteps] using
        (NaturalRun.step t90 (.step t91 (.step t92 (.done _)))),by simp [member,hn]⟩
  | cons f fs ih =>
    cases input with
    | @cons _ head tail _ _ hp hf ht =>
      let frames := (⟨pc,.r3,saved⟩::stack)
      obtain ⟨e1,flag,len1,core,htag⟩ := edge_return hf query next a d hn
        ⟨head,b,a,d⟩ 96 frames source
      have t90 : tickNatural program (state heap next a b c d frames source 90)=
          some ⟨state heap next a b c d frames source 93,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,hp,tagBranch]
      have t93 : tickNatural program (state heap next a b c d frames source 93)=
          some ⟨state heap next a b a d frames source 94,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set]
      have t94 : tickNatural program (state heap next a b a d frames source 94)=
          some ⟨state heap next head b a d frames source 95,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,hp]
      have t95 : tickNatural program (state heap next head b a d frames source 95)=
          some ⟨state heap next head b a d (⟨96,.r3,⟨head,b,a,d⟩⟩::frames) source 100,[],0⟩ := by
        simp [tickNatural,program,state]
      have preRun := NaturalRun.step t90 (.step t93 (.step t94 (.step t95 core)))
      have branch : tickNatural program (state (heap++e1) (next+e1.length) head b a flag frames source 96)=
          some ⟨state (heap++e1) (next+e1.length) head b a flag frames source
            (if edgeEq f e then 99 else 97),[],0⟩ := by
        cases h : edgeEq f e <;> simp [tickNatural,program,state,Registers.get,htag,h,tagBranch]
      by_cases h : edgeEq f e=true
      · have ret : tickNatural program (state (heap++e1) (next+e1.length) head b a flag frames source 99)=
            some ⟨state (heap++e1) (next+e1.length) saved.a saved.b saved.c flag stack source pc,[],0⟩ := by
          simp [tickNatural,program,state,frames,Registers.get,Registers.set]
        simp only [h,ite_true] at branch
        refine ⟨e1,flag,by simpa [memberCells,h] using len1,?_,?_⟩
        · convert run_append preRun (.step branch (.step ret (.done _))) using 1 <;>
            simp [memberSteps,h]
        · simpa [member,h] using htag
      · obtain ⟨e2,root,len2,body,out⟩ := ih (edgeList_extend ht e1) (edge_extend query e1)
          (next+e1.length) a flag (by simp [hn]) ⟨tail,b,a,flag⟩ 99 frames
        have t97 : tickNatural program (state (heap++e1) (next+e1.length) head b a flag frames source 97)=
            some ⟨state (heap++e1) (next+e1.length) tail b a flag frames source 98,[],0⟩ := by
          simp [tickNatural,program,state,Registers.get,Registers.set,lookup_extend hp e1]
        have t98 : tickNatural program (state (heap++e1) (next+e1.length) tail b a flag frames source 98)=
            some ⟨state (heap++e1) (next+e1.length) tail b a flag
              (⟨99,.r3,⟨tail,b,a,flag⟩⟩::frames) source 90,[],0⟩ := by
          simp [tickNatural,program,state]
        have t99 : tickNatural program
            (state ((heap++e1)++e2) (next+e1.length+e2.length) tail b a root frames source 99)=
            some ⟨state ((heap++e1)++e2) (next+e1.length+e2.length)
              saved.a saved.b saved.c root stack source pc,[],0⟩ := by
          simp [tickNatural,program,state,frames,Registers.get,Registers.set]
        simp only [h] at branch
        refine ⟨e1++e2,root,by simp [memberCells,h,len1,len2],?_,?_⟩
        · convert run_append preRun (.step branch (.step t97 (.step t98
            (run_append body (.step t99 (.done _)))))) using 1 <;>
            simp [memberSteps,h,List.append_assoc,state]
          all_goals omega
        · simpa [member,h,List.append_assoc] using out

end DirectedFlowCutGap.SupportRecoveryProgram
