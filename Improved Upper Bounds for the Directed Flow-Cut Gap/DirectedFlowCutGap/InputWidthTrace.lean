import DirectedFlowCutGap.InputWidthCalls

namespace DirectedFlowCutGap.InputWidthProgram
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor

theorem width_return (rows : List Fraction) {heap : NaturalHeap} {a : ℕ}
    (input : WordPairTableRead.Table heap a (IndexedRationalRead.fields rows))
    (next b c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 208)
    (stack : List (Frame ℕ 208)) (source : Bits) :
    ∃ ext root,ext.length=cells rows ∧
      NaturalRun program (steps rows) (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 190) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      BoolList (heap++ext) root (BinaryFractionalGuesses.widthList rows).1 := by
  induction rows generalizing heap a next b c d saved pc stack with
  | nil =>
    cases input with
    | nil hp =>
      refine ⟨[.nil],next,rfl,?_,.nil (by simp [hn])⟩
      have t190 : tickNatural program (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 190)=
          some ⟨state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 191,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,hp,tagBranch]
      have t191 : tickNatural program (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 191)=
          some ⟨state (heap++[.nil]) (next+1) a b c next (⟨pc,.r3,saved⟩::stack) source 192,[],0⟩ := by
        simp [tickNatural,program,state,Registers.set,allocateNatural,Recipe.cell]
      have t192 : tickNatural program
          (state (heap++[.nil]) (next+1) a b c next (⟨pc,.r3,saved⟩::stack) source 192)=
          some ⟨state (heap++[.nil]) (next+1) saved.a saved.b saved.c next stack source pc,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set]
      exact .step t190 (.step t191 (.step t192 (.done _)))
  | cons q qs ih =>
    simp only [IndexedRationalRead.fields,List.map_cons] at input
    cases input with
    | @cons a cost tail num den _ _ _ pair record nrep drep rest =>
      let frame : Frame ℕ 208 := ⟨pc,.r3,saved⟩
      obtain ⟨eh,head,hlen,hrun,hs⟩ := width_call ⟨num,den,record,nrep,drep⟩ next b a d hn
        ⟨cost,b,a,d⟩ 197 (frame::stack) source
      obtain ⟨et,tailWidth,tlen,trun,ts⟩ := ih (BinaryIndexedPairRead.table_extend rest eh)
        (next+eh.length) head a head (by simp [hn]) ⟨tail,head,a,head⟩ 200 (frame::stack)
      obtain ⟨em,root,mlen,mrun,answer⟩ := max_call (boolList_extend hs et) ts
        (next+eh.length+et.length) a tailWidth (by simp [hn,Nat.add_assoc])
        ⟨head,tailWidth,a,tailWidth⟩ 203 (frame::stack) source
      have t190 : tickNatural program (state heap next a b c d (frame::stack) source 190)=
          some ⟨state heap next a b c d (frame::stack) source 194,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,pair,tagBranch]
      have t194 : tickNatural program (state heap next a b c d (frame::stack) source 194)=
          some ⟨state heap next a b a d (frame::stack) source 195,[],0⟩ := by rfl
      have t195 : tickNatural program (state heap next a b a d (frame::stack) source 195)=
          some ⟨state heap next cost b a d (frame::stack) source 196,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,pair]
      have t196 : tickNatural program (state heap next cost b a d (frame::stack) source 196)=
          some ⟨state heap next cost b a d (⟨197,.r3,⟨cost,b,a,d⟩⟩::frame::stack) source 126,[],0⟩ := by rfl
      have t197 : tickNatural program (state (heap++eh) (next+eh.length) cost b a head (frame::stack) source 197)=
          some ⟨state (heap++eh) (next+eh.length) cost head a head (frame::stack) source 198,[],0⟩ := by rfl
      have t198 : tickNatural program (state (heap++eh) (next+eh.length) cost head a head (frame::stack) source 198)=
          some ⟨state (heap++eh) (next+eh.length) tail head a head (frame::stack) source 199,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,lookup_extend pair eh]
      have t199 : tickNatural program (state (heap++eh) (next+eh.length) tail head a head (frame::stack) source 199)=
          some ⟨state (heap++eh) (next+eh.length) tail head a head
            (⟨200,.r3,⟨tail,head,a,head⟩⟩::frame::stack) source 190,[],0⟩ := by rfl
      have t200 : tickNatural program
          (state ((heap++eh)++et) (next+eh.length+et.length) tail head a tailWidth (frame::stack) source 200)=
          some ⟨state ((heap++eh)++et) (next+eh.length+et.length) head head a tailWidth (frame::stack) source 201,[],0⟩ := by rfl
      have t201 : tickNatural program
          (state ((heap++eh)++et) (next+eh.length+et.length) head head a tailWidth (frame::stack) source 201)=
          some ⟨state ((heap++eh)++et) (next+eh.length+et.length) head tailWidth a tailWidth (frame::stack) source 202,[],0⟩ := by rfl
      have t202 : tickNatural program
          (state ((heap++eh)++et) (next+eh.length+et.length) head tailWidth a tailWidth (frame::stack) source 202)=
          some ⟨state ((heap++eh)++et) (next+eh.length+et.length) head tailWidth a tailWidth
            (⟨203,.r3,⟨head,tailWidth,a,tailWidth⟩⟩::frame::stack) source 182,[],0⟩ := by rfl
      have t203 : tickNatural program
          (state (((heap++eh)++et)++em) (next+eh.length+et.length+em.length) head tailWidth a root (frame::stack) source 203)=
          some ⟨state (((heap++eh)++et)++em) (next+eh.length+et.length+em.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
        simp [tickNatural,program,state,frame,Registers.get,Registers.set]
      refine ⟨eh++et++em,root,by simp [cells,hlen,tlen,mlen,Nat.add_assoc],?_,?_⟩
      · have all := NaturalRun.step t190 (.step t194 (.step t195 (.step t196 (run_append hrun
          (.step t197 (.step t198 (.step t199 (run_append trun
            (.step t200 (.step t201 (.step t202 (run_append mrun (.step t203 (.done _))))))))))))))
        convert all using 1 <;> simp [steps,state,List.append_assoc,Nat.add_assoc]
        omega
      · simpa only [BinaryFractionalGuesses.widthList,List.append_assoc] using answer
end DirectedFlowCutGap.InputWidthProgram
