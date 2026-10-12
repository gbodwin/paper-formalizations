import DirectedFlowCutGap.MaskedRationalRowHead

namespace DirectedFlowCutGap.MaskedRationalRow
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

theorem row_return {xs : List Fraction} {mask : List Bool} {heap : NaturalHeap} {a b : ℕ}
    (row : StoredList heap a xs) (flags : BoolList heap b mask) (aligned : xs.length=mask.length)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 24)
    (stack : List (Frame ℕ 24)) (source : Bits) :
    ∃ ext root,ext.length=cells mask ∧
      NaturalRun program (steps mask)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 0) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      StoredList (heap++ext) root (result xs mask) := by
  induction xs generalizing mask heap a b next c d saved pc stack with
  | nil =>
    have hm : mask=[] := by simpa using aligned.symm
    subst mask
    cases row with
    | nil hp =>
      let frames : List (Frame ℕ 24) := ⟨pc,.r3,saved⟩::stack
      have t0 : tickNatural program (state heap next a b c d frames source 0)=
          some ⟨state heap next a b c d frames source 1,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,hp,tagBranch]
      have t1 : tickNatural program (state heap next a b c d frames source 1)=
          some ⟨state (heap++[.nil]) (next+1) a b c next frames source 2,[],0⟩ := by
        simp [tickNatural,program,state,Registers.set,Recipe.cell,allocateNatural]
      have t2 : tickNatural program (state (heap++[.nil]) (next+1) a b c next frames source 2)=
          some ⟨state (heap++[.nil]) (next+1) saved.a saved.b saved.c next stack source pc,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,frames]
      exact ⟨[.nil],next,rfl,.step t0 (.step t1 (.step t2 (.done _))),.nil (by simp [hn])⟩
  | cons x xs ih =>
    cases mask with
    | nil => simp at aligned
    | cons enabled bs =>
      have al : xs.length=bs.length := by simpa using aligned
      cases row with
      | @cons a ax tx x xs hx hxr hxt =>
        cases flags with
        | @cons b bf bt enabled bs hm hf hft =>
          let frames : List (Frame ℕ 24) := ⟨pc,.r3,saved⟩::stack
          let e0 : NaturalHeap := [.pair a b]
          let h0 := heap++e0
          let n0 := next+1
          have dense0 : n0=h0.length := by simp [n0,h0,e0,hn]
          obtain ⟨et,rt,lt,tailRun,tailRep⟩ := ih (list_extend hxt e0) (boolList_extend hft e0) al
            n0 next d dense0 ⟨tx,bt,next,d⟩ 7 frames
          let h1 := h0++et
          let n1 := n0+et.length
          let e1 : NaturalHeap := [.pair next rt]
          let h2 := h1++e1
          let n2 := n1+1
          have dense1 : n1=h1.length := by simp [n1,h1,dense0]
          have dense2 : n2=h2.length := by simp [n2,h2,e1,dense1]
          have original : h2[next]?=some (.pair a b) := by
            apply lookup_extend (h:=h1)
            apply lookup_extend (h:=h0)
            simp [h0,e0,hn]
          have ctx : h2[n1]?=some (.pair next rt) := by simp [h2,e1,dense1]
          have flag : h2[bf]?=some (.flag enabled) := lookup_extend (lookup_extend (lookup_extend hf e0) et) e1
          have entry : h2[a]?=some (.pair ax tx) := lookup_extend (lookup_extend (lookup_extend hx e0) et) e1
          obtain ⟨eh,rh,lh,headRun,headRep⟩ := head_return enabled (d:=rt) flag original entry ctx
            (stored_extend (stored_extend (stored_extend hxr e0) et) e1) (list_extend tailRep e1)
            dense2 saved pc stack source
          have t0 : tickNatural program (state heap next a b c d frames source 0)=
              some ⟨state heap next a b c d frames source 3,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,hx,tagBranch]
          have t3 : tickNatural program (state heap next a b c d frames source 3)=
              some ⟨state h0 n0 a b next d frames source 4,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,Registers.set,Recipe.cell,allocateNatural,h0,e0,n0]
          have hx0 : h0[a]?=some (.pair ax tx) := lookup_extend hx e0
          have hm0 : h0[b]?=some (.pair bf bt) := lookup_extend hm e0
          have t4 : tickNatural program (state h0 n0 a b next d frames source 4)=
              some ⟨state h0 n0 tx b next d frames source 5,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,Registers.set,hx0]
          have t5 : tickNatural program (state h0 n0 tx b next d frames source 5)=
              some ⟨state h0 n0 tx bt next d frames source 6,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,Registers.set,hm0]
          have t6 : tickNatural program (state h0 n0 tx bt next d frames source 6)=
              some ⟨state h0 n0 tx bt next d (⟨7,.r3,⟨tx,bt,next,d⟩⟩::frames) source 0,[],0⟩ := by
            simp [tickNatural,program,state]
          have t7 : tickNatural program (state h1 n1 tx bt next rt frames source 7)=
              some ⟨state h2 n2 tx bt n1 rt frames source 8,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,Registers.set,Recipe.cell,allocateNatural,h2,e1,n2]
          have t8 : tickNatural program (state h2 n2 tx bt n1 rt frames source 8)=
              some ⟨state h2 n2 next bt n1 rt frames source 9,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,Registers.set,ctx]
          have t9 : tickNatural program (state h2 n2 next bt n1 rt frames source 9)=
              some ⟨state h2 n2 next b n1 rt frames source 10,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,Registers.set,original]
          have hm2 : h2[b]?=some (.pair bf bt) := lookup_extend (lookup_extend (lookup_extend hm e0) et) e1
          have t10 : tickNatural program (state h2 n2 next b n1 rt frames source 10)=
              some ⟨state h2 n2 next bf n1 rt frames source 11,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,Registers.set,hm2]
          have whole := NaturalRun.step t0 (.step t3 (.step t4 (.step t5 (.step t6
            (run_append tailRun (.step t7 (.step t8 (.step t9 (.step t10 headRun)))))))))
          let ext := e0++et++e1++eh
          have heaps : heap++ext=h2++eh := by simp [ext,h2,h1,h0,List.append_assoc]
          have sizes : next+ext.length=n2+eh.length := by simp [ext,e0,e1,n2,n1,n0];omega
          refine ⟨ext,rh,?_,?_,?_⟩
          · simp [ext,e0,e1,cells,lt,lh]
            split <;> omega
          · rw [heaps,sizes]
            convert whole using 1 <;> simp [steps]
            split <;> omega
          · rw [heaps]
            simpa [result,List.zipWith_cons_cons] using headRep
end DirectedFlowCutGap.MaskedRationalRow
