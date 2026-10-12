import DirectedFlowCutGap.ScalarQuotientRowCall

namespace DirectedFlowCutGap.ScalarQuotientRow
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

theorem row_return (mode : Bool) (scalar : Fraction) {xs : List Fraction}
    {heap : NaturalHeap} {a b : ℕ} (row : StoredList heap a xs) (sc : Stored heap b scalar)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 182)
    (stack : List (Frame ℕ 182)) (source : Bits) :
    ∃ ext root,ext.length=cells mode scalar xs ∧
      NaturalRun (program mode) (steps mode scalar xs)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 164) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      StoredList (heap++ext) root (result mode scalar xs) := by
  induction xs generalizing heap a b next c d saved pc stack with
  | nil =>
    cases row with
    | nil hp =>
      let frames : List (Frame ℕ 182) := ⟨pc,.r3,saved⟩::stack
      let ext : NaturalHeap := [.nil]
      have t164 : tickNatural (program mode) (state heap next a b c d frames source 164)=
          some ⟨state heap next a b c d frames source 165,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,hp,tagBranch]
      have t165 : tickNatural (program mode) (state heap next a b c d frames source 165)=
          some ⟨state (heap++ext) (next+1) a b c next frames source 166,[],0⟩ := by
        simp [tickNatural,program,state,Registers.set,Recipe.cell,allocateNatural,ext]
      have t166 : tickNatural (program mode) (state (heap++ext) (next+1) a b c next frames source 166)=
          some ⟨state (heap++ext) (next+1) saved.a saved.b saved.c next stack source pc,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,frames]
      refine ⟨ext,next,rfl,?_,?_⟩
      · simpa [steps,ext] using NaturalRun.step t164 (.step t165 (.step t166 (.done _)))
      · exact .nil (by simp [ext,hn])
  | cons x xs ih =>
    cases row with
    | @cons a ax tx x xs hx hxr hxt =>
      let frames : List (Frame ℕ 182) := ⟨pc,.r3,saved⟩::stack
      obtain ⟨et,rt,lt,tailRun,tailRep⟩ := ih hxt sc next ax d hn ⟨tx,b,ax,d⟩ 170 frames
      let h1 := heap++et
      let n1 := next+et.length
      have dense1 : n1=h1.length := by simp [n1,h1,hn]
      obtain ⟨eq,rq,lq,quotRun,quotRep⟩ := divide_head mode scalar x
        (stored_extend hxr et) (stored_extend sc et) n1 rt dense1 frames source
      let h2 := h1++eq
      let n2 := n1+eq.length
      let e2 : NaturalHeap := [.pair rq rt]
      let h3 := h2++e2
      let na := if mode then b else ax
      let nb := if mode then ax else b
      have t164 : tickNatural (program mode) (state heap next a b c d frames source 164)=
          some ⟨state heap next a b c d frames source 167,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,hx,tagBranch]
      have t167 : tickNatural (program mode) (state heap next a b c d frames source 167)=
          some ⟨state heap next a b ax d frames source 168,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,hx]
      have t168 : tickNatural (program mode) (state heap next a b ax d frames source 168)=
          some ⟨state heap next tx b ax d frames source 169,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,hx]
      have t169 : tickNatural (program mode) (state heap next tx b ax d frames source 169)=
          some ⟨state heap next tx b ax d (⟨170,.r3,⟨tx,b,ax,d⟩⟩::frames) source 164,[],0⟩ := by
        simp [tickNatural,program,state]
      have t170 : tickNatural (program mode) (state h1 n1 tx b ax rt frames source 170)=
          some ⟨state h1 n1 ax b ax rt frames source 171,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set]
      have t171 : tickNatural (program mode) (state h1 n1 ax b ax rt frames source 171)=
          some ⟨state h1 n1 ax b rt rt frames source 172,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set]
      have t176 : tickNatural (program mode) (state h2 n2 na nb rt rq frames source 176)=
          some ⟨state h3 (n2+1) na nb rt n2 frames source 177,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,Recipe.cell,allocateNatural,h3,e2]
      have t177 : tickNatural (program mode) (state h3 (n2+1) na nb rt n2 frames source 177)=
          some ⟨state h3 (n2+1) saved.a saved.b saved.c n2 stack source pc,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,frames]
      have whole := NaturalRun.step t164 (.step t167 (.step t168 (.step t169
        (run_append mode tailRun (.step t170 (.step t171
          (run_append mode quotRun (.step t176 (.step t177 (.done _))))))))))
      let ext := et++eq++e2
      have eh : heap++ext=h3 := by simp [ext,h3,h2,h1,List.append_assoc]
      have en : next+ext.length=n2+1 := by simp [ext,e2,n2,n1];omega
      refine ⟨ext,n2,by simp [ext,e2,cells,lt,lq];omega,?_,?_⟩
      · rw [eh,en]
        convert whole using 1 <;> simp [steps]
        split <;> omega
      · rw [eh]
        apply StoredList.cons (head:=rq) (tail:=rt)
        · have dense2 : n2=h2.length := by simp [n2,h2,dense1]
          simp [h3,e2,dense2]
        · exact stored_extend quotRep e2
        · exact list_extend (list_extend tailRep eq) e2
end DirectedFlowCutGap.ScalarQuotientRow
