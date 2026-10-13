import DirectedFlowCutGap.PositiveMinimumProgram

namespace DirectedFlowCutGap.RetainedArgminProgram
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor

theorem run_high_pc (xs : List Item) (initial : NaturalState 194)
    (pc0 : initial.pc=178) (hn : initial.next=initial.heap.length)
    (input : ItemList initial.heap initial.registers.a xs) (empty : initial.stack=[]) :
    ∃ out, NaturalRun program (steps xs) initial [] out ∧
      Selected out.heap out.registers.d (select xs) ∧
      ItemList out.heap initial.registers.a xs ∧ out.source=initial.source ∧ out.stack=[] ∧
      out.next=out.heap.length ∧
      (∃ ext,out.heap=initial.heap++ext ∧ ext.length=cells xs) ∧
      (out.pc=175 ∨ out.pc=177) ∧ tickNatural program out=none := by
  cases initial with
  | mk heap next regs stack pc source =>
    cases regs with
    | mk a b c d =>
      simp only at pc0 hn input empty
      subst pc;subst stack
      cases xs with
      | nil =>
        cases input with
        | nil hnil =>
          have t178 : tickNatural program (state heap next a b c d [] source 178)=
              some ⟨state heap next a b c d [] source 174,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,hnil,tagBranch]
          have t174 : tickNatural program (state heap next a b c d [] source 174)=
              some ⟨state (heap++[.nil]) (next+1) a b c next [] source 175,[],0⟩ := by
            simp [tickNatural,program,state,Registers.set,allocateNatural,Recipe.cell]
          refine ⟨state (heap++[.nil]) (next+1) a b c next [] source 175,
            .step t178 (.step t174 (.done _)),?_,?_,rfl,rfl,?_,⟨[.nil],rfl,rfl⟩,Or.inl rfl,rfl⟩
          · simp [Selected,select,state,hn]
          · exact list_extend (.nil hnil) _
          · simp [state,hn]
      | cons x xs =>
        cases input with
        | @cons a item tail x xs hp hi ht =>
          have t178 : tickNatural program (state heap next a b c d [] source 178)=
              some ⟨state heap next a b c d [] source 179,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,hp,tagBranch]
          have t179 : tickNatural program (state heap next a b c d [] source 179)=
              some ⟨state heap next a tail c d [] source 180,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,Registers.set,hp]
          have t180 : tickNatural program (state heap next a tail c d [] source 180)=
              some ⟨state heap next item tail c d [] source 160,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,Registers.set,hp]
          obtain ⟨ext,out,len,run,he,hnext,selected,src,frames,hpc,halt⟩ := scan_high xs x hi ht next c d hn source
          refine ⟨out,?_,selected,?_,src,frames,?_,⟨ext,he,len⟩,Or.inr hpc,halt⟩
          · simpa [steps,state,Nat.add_assoc] using NaturalRun.step t178 (.step t179 (.step t180 run))
          · rw [he];exact list_extend (.cons hp hi ht) ext
          · rw [hnext,he];simp [hn]

end DirectedFlowCutGap.RetainedArgminProgram
