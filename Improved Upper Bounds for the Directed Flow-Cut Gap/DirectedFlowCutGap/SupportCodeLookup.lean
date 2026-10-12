import DirectedFlowCutGap.SupportRecoveryCalls

/-! First-key lookup traverses the actual retained table and returns its original
code pointer. Padded words are compared by the relocated binary program. -/
namespace DirectedFlowCutGap.SupportRecoveryProgram
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor GraphWalkExtension

theorem lookup_return {heap : NaturalHeap} {a b : ℕ} {xs : List Code} {u : Bits}
    (input : Codes heap a xs) (word : BoolList heap b u)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 280)
    (stack : List (Frame ℕ 280)) (source : Bits) :
    ∃ ext root,ext.length=lookupCells u xs ∧
      NaturalRun program (lookupSteps u xs)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 150) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      StoredOption (heap++ext) root (lookup u xs) := by
  induction xs generalizing heap a b next c d saved pc stack with
  | nil =>
    cases input with
    | nil hp =>
      let frames := (⟨pc,.r3,saved⟩::stack)
      have t150 : tickNatural program (state heap next a b c d frames source 150)=
          some ⟨state heap next a b c d frames source 151,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,hp,tagBranch]
      have t151 : tickNatural program (state heap next a b c d frames source 151)=
          some ⟨state (heap++[.nil]) (next+1) a b c next frames source 152,[],0⟩ := by
        simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.set]
      have t152 : tickNatural program (state (heap++[.nil]) (next+1) a b c next frames source 152)=
          some ⟨state (heap++[.nil]) (next+1) saved.a saved.b saved.c next stack source pc,[],0⟩ := by
        simp [tickNatural,program,state,frames,Registers.get,Registers.set]
      exact ⟨[.nil],next,rfl,by simpa [lookupSteps] using
        (NaturalRun.step t150 (.step t151 (.step t152 (.done _)))),by simp [StoredOption,lookup,hn]⟩
  | cons x xs ih =>
    cases input with
    | @cons _ head tail _ _ hp hx ht =>
      obtain ⟨vertex,edges,he,hv,hedges⟩ := hx
      let frames := (⟨pc,.r3,saved⟩::stack)
      obtain ⟨e1,tag,len1,cmp,htag⟩ := compare_return hv word next a d hn
        ⟨vertex,b,a,d⟩ 157 frames source
      have t150 : tickNatural program (state heap next a b c d frames source 150)=
          some ⟨state heap next a b c d frames source 153,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,hp,tagBranch]
      have t153 : tickNatural program (state heap next a b c d frames source 153)=
          some ⟨state heap next a b a d frames source 154,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set]
      have t154 : tickNatural program (state heap next a b a d frames source 154)=
          some ⟨state heap next head b a d frames source 155,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,hp]
      have t155 : tickNatural program (state heap next head b a d frames source 155)=
          some ⟨state heap next vertex b a d frames source 156,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,he]
      have t156 : tickNatural program (state heap next vertex b a d frames source 156)=
          some ⟨state heap next vertex b a d (⟨157,.r3,⟨vertex,b,a,d⟩⟩::frames) source 84,[],0⟩ := by
        simp [tickNatural,program,state]
      have preRun := NaturalRun.step t150 (.step t153 (.step t154 (.step t155 (.step t156 cmp))))
      have branch : tickNatural program (state (heap++e1) (next+e1.length) vertex b a tag frames source 157)=
          some ⟨state (heap++e1) (next+e1.length) vertex b a tag frames source
            (if same x.1 u then 158 else 160),[],0⟩ := by
        cases ho : BinaryComparisonProgram.order x.1 u <;>
          simp [tickNatural,program,state,Registers.get,htag,ho,BinaryComparisonProgram.tag,tagBranch,same]
      by_cases hs : same x.1 u=true
      · have t158 : tickNatural program (state (heap++e1) (next+e1.length) vertex b a tag frames source 158)=
            some ⟨state (heap++e1) (next+e1.length) vertex b a head frames source 159,[],0⟩ := by
          simp [tickNatural,program,state,Registers.get,Registers.set,lookup_extend hp e1]
        have t159 : tickNatural program (state (heap++e1) (next+e1.length) vertex b a head frames source 159)=
            some ⟨state (heap++e1) (next+e1.length) saved.a saved.b saved.c head stack source pc,[],0⟩ := by
          simp [tickNatural,program,state,frames,Registers.get,Registers.set]
        simp only [hs,ite_true] at branch
        refine ⟨e1,head,by simpa [lookupCells,hs] using len1,?_,?_⟩
        · convert run_append preRun (.step branch (.step t158 (.step t159 (.done _)))) using 1 <;>
            simp [lookupSteps,hs]
        · exact show StoredOption (heap++e1) head (lookup u (x::xs)) from
            by simpa [lookup,hs,StoredOption] using
              (code_extend (show StoredCode heap head x from ⟨vertex,edges,he,hv,hedges⟩) e1)
      · obtain ⟨e2,root,len2,body,out⟩ := ih (codes_extend ht e1) (boolList_extend word e1)
          (next+e1.length) a tag (by simp [hn]) ⟨tail,b,a,tag⟩ 162 frames
        have t160 : tickNatural program (state (heap++e1) (next+e1.length) vertex b a tag frames source 160)=
            some ⟨state (heap++e1) (next+e1.length) tail b a tag frames source 161,[],0⟩ := by
          simp [tickNatural,program,state,Registers.get,Registers.set,lookup_extend hp e1]
        have t161 : tickNatural program (state (heap++e1) (next+e1.length) tail b a tag frames source 161)=
            some ⟨state (heap++e1) (next+e1.length) tail b a tag
              (⟨162,.r3,⟨tail,b,a,tag⟩⟩::frames) source 150,[],0⟩ := by
          simp [tickNatural,program,state]
        have t162 : tickNatural program
            (state ((heap++e1)++e2) (next+e1.length+e2.length) tail b a root frames source 162)=
            some ⟨state ((heap++e1)++e2) (next+e1.length+e2.length)
              saved.a saved.b saved.c root stack source pc,[],0⟩ := by
          simp [tickNatural,program,state,frames,Registers.get,Registers.set]
        simp only [hs] at branch
        refine ⟨e1++e2,root,by simp [lookupCells,hs,len1,len2],?_,?_⟩
        · convert run_append preRun (.step branch (.step t160 (.step t161
            (run_append body (.step t162 (.done _)))))) using 1 <;>
            simp [lookupSteps,hs,List.append_assoc,state]
          all_goals omega
        · simpa [lookup,hs,List.append_assoc] using out

end DirectedFlowCutGap.SupportRecoveryProgram
