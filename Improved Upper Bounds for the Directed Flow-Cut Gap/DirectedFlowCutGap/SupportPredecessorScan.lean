import DirectedFlowCutGap.SupportPredecessorPrefix

namespace DirectedFlowCutGap.SupportRecoveryProgram
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor GraphWalkExtension

theorem predecessor_return {heap : NaturalHeap} {a b : ℕ} {xs : List Code} {u : Bits}
    {adjacency : List Bits} {es : List (Bits × Bits)}
    (input : Codes heap a xs) (context : StoredPredContext heap b adjacency es u)
    (hi : value u<adjacency.length)
    (hj : ∀ x∈xs,value x.1<(adjacency[value u]).length)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 280)
    (stack : List (Frame ℕ 280)) (source : Bits) :
    ∃ ext root,ext.length=predCells adjacency es u xs ∧
      NaturalRun program (predSteps adjacency es u xs)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 170) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      StoredOption (heap++ext) root (predecessor adjacency es u xs) := by
  induction xs generalizing heap a b next c d saved pc stack with
  | nil =>
    cases input with
    | nil hp =>
      let frames := (⟨pc,.r3,saved⟩::stack)
      have t170 : tickNatural program (state heap next a b c d frames source 170)=
          some ⟨state heap next a b c d frames source 151,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,hp,tagBranch]
      have t151 : tickNatural program (state heap next a b c d frames source 151)=
          some ⟨state (heap++[.nil]) (next+1) a b c next frames source 152,[],0⟩ := by
        simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.set]
      have t152 : tickNatural program (state (heap++[.nil]) (next+1) a b c next frames source 152)=
          some ⟨state (heap++[.nil]) (next+1) saved.a saved.b saved.c next stack source pc,[],0⟩ := by
        simp [tickNatural,program,state,frames,Registers.get,Registers.set]
      exact ⟨[.nil],next,rfl,by simpa [predSteps] using
        (NaturalRun.step t170 (.step t151 (.step t152 (.done _)))),by simp [StoredOption,predecessor,hn]⟩
  | cons x xs ih =>
    cases input with
    | @cons _ head tail _ _ hp hx ht =>
      let frames := (⟨pc,.r3,saved⟩::stack)
      obtain ⟨e1,flag,ctx,len1,preRun,scratch,htag⟩ := predecessor_prefix hp hx context hi
        (hj x (by simp)) next c d hn frames source
      have branch : tickNatural program (state (heap++e1) (next+e1.length) (next+1) ctx next flag frames source 178)=
          some ⟨state (heap++e1) (next+e1.length) (next+1) ctx next flag frames source
            (if support adjacency es u x.1 then 185 else 179),[],0⟩ := by
        cases h : support adjacency es u x.1 <;>
          simp [tickNatural,program,state,Registers.get,htag,h,tagBranch]
      by_cases h : support adjacency es u x.1=true
      · have t185 : tickNatural program
            (state (heap++e1) (next+e1.length) (next+1) ctx next flag frames source 185)=
            some ⟨state (heap++e1) (next+e1.length) a ctx next flag frames source 186,[],0⟩ := by
          simp [tickNatural,program,state,Registers.get,Registers.set,scratch]
        have t186 : tickNatural program (state (heap++e1) (next+e1.length) a ctx next flag frames source 186)=
            some ⟨state (heap++e1) (next+e1.length) a ctx next head frames source 187,[],0⟩ := by
          simp [tickNatural,program,state,Registers.get,Registers.set,lookup_extend hp e1]
        have t187 : tickNatural program (state (heap++e1) (next+e1.length) a ctx next head frames source 187)=
            some ⟨state (heap++e1) (next+e1.length) saved.a saved.b saved.c head stack source pc,[],0⟩ := by
          simp [tickNatural,program,state,frames,Registers.get,Registers.set]
        simp only [h,ite_true] at branch
        refine ⟨e1,head,by simpa [predCells,h] using len1,?_,?_⟩
        · convert run_append preRun (.step branch (.step t185 (.step t186 (.step t187 (.done _))))) using 1 <;>
            simp [predSteps,h]
        · simpa [predecessor,h,StoredOption] using code_extend hx e1
      · obtain ⟨e2,root,len2,body,out⟩ := ih (codes_extend ht e1) (predContext_extend context e1)
          (fun y hy => hj y (by simp [hy])) (next+e1.length) next flag (by simp [hn])
          ⟨tail,b,next,flag⟩ 183 frames
        have t179 : tickNatural program
            (state (heap++e1) (next+e1.length) (next+1) ctx next flag frames source 179)=
            some ⟨state (heap++e1) (next+e1.length) a ctx next flag frames source 180,[],0⟩ := by
          simp [tickNatural,program,state,Registers.get,Registers.set,scratch]
        have t180 : tickNatural program (state (heap++e1) (next+e1.length) a ctx next flag frames source 180)=
            some ⟨state (heap++e1) (next+e1.length) tail ctx next flag frames source 181,[],0⟩ := by
          simp [tickNatural,program,state,Registers.get,Registers.set,lookup_extend hp e1]
        have t181 : tickNatural program (state (heap++e1) (next+e1.length) tail ctx next flag frames source 181)=
            some ⟨state (heap++e1) (next+e1.length) tail b next flag frames source 182,[],0⟩ := by
          simp [tickNatural,program,state,Registers.get,Registers.set,scratch]
        have t182 : tickNatural program (state (heap++e1) (next+e1.length) tail b next flag frames source 182)=
            some ⟨state (heap++e1) (next+e1.length) tail b next flag
              (⟨183,.r3,⟨tail,b,next,flag⟩⟩::frames) source 170,[],0⟩ := by
          simp [tickNatural,program,state]
        have t183 : tickNatural program
            (state ((heap++e1)++e2) (next+e1.length+e2.length) tail b next root frames source 183)=
            some ⟨state ((heap++e1)++e2) (next+e1.length+e2.length)
              saved.a saved.b saved.c root stack source pc,[],0⟩ := by
          simp [tickNatural,program,state,frames,Registers.get,Registers.set]
        simp only [h] at branch
        refine ⟨e1++e2,root,by simp [predCells,h,len1,len2],?_,?_⟩
        · convert run_append preRun (.step branch (.step t179 (.step t180 (.step t181 (.step t182
            (run_append body (.step t183 (.done _)))))))) using 1 <;>
            simp [predSteps,h,List.append_assoc,state]
          all_goals omega
        · simpa [predecessor,h,List.append_assoc] using out

end DirectedFlowCutGap.SupportRecoveryProgram
