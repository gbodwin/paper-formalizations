import DirectedFlowCutGap.ObjectiveProductListProgram

namespace DirectedFlowCutGap.ObjectiveProductList
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

theorem products_return {xs ys : List Fraction} {heap : NaturalHeap} {a b : ℕ}
    (left : StoredList heap a xs) (right : StoredList heap b ys) (aligned : xs.length=ys.length)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 150)
    (stack : List (Frame ℕ 150)) (source : Bits) :
    ∃ ext root,ext.length=cells xs ys ∧
      NaturalRun program (steps xs ys)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 132) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      StoredList (heap++ext) root (products xs ys) := by
  induction xs generalizing ys heap a b next c d saved pc stack with
  | nil =>
    cases left with
    | nil hp =>
      let frames : List (Frame ℕ 150) := ⟨pc,.r3,saved⟩::stack
      let ext : NaturalHeap := [.nil]
      have t132 : tickNatural program (state heap next a b c d frames source 132)=
          some ⟨state heap next a b c d frames source 133,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,hp,tagBranch]
      have t133 : tickNatural program (state heap next a b c d frames source 133)=
          some ⟨state (heap++ext) (next+1) a b c next frames source 134,[],0⟩ := by
        simp [tickNatural,program,state,Registers.set,Recipe.cell,allocateNatural,ext]
      have t134 : tickNatural program (state (heap++ext) (next+1) a b c next frames source 134)=
          some ⟨state (heap++ext) (next+1) saved.a saved.b saved.c next stack source pc,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,frames]
      refine ⟨ext,next,rfl,?_,?_⟩
      · simpa [steps,ext] using NaturalRun.step t132 (.step t133 (.step t134 (.done _)))
      · exact .nil (by simp [ext,hn])
  | cons x xs ih =>
    cases ys with
    | nil => simp at aligned
    | cons y ys =>
      have al : xs.length=ys.length := by simpa using aligned
      cases left with
      | @cons a ax tx x xs hx hxr hxt =>
        cases right with
        | @cons b byp ty y ys hy hyr hyt =>
          let frames : List (Frame ℕ 150) := ⟨pc,.r3,saved⟩::stack
          let e0 : NaturalHeap := [.pair a b]
          let h0 := heap++e0
          let n0 := next+1
          have dense0 : n0=h0.length := by simp [n0,h0,e0,hn]
          obtain ⟨et,rt,lt,tailRun,tailRep⟩ := ih (list_extend hxt e0) (list_extend hyt e0) al
            n0 next d dense0 ⟨tx,ty,next,d⟩ 139 frames
          let h1 := h0++et
          let n1 := n0+et.length
          have dense1 : n1=h1.length := by simp [n1,h1,dense0]
          have px : Stored h1 ax x := stored_extend (stored_extend hxr e0) et
          have py : Stored h1 byp y := stored_extend (stored_extend hyr e0) et
          obtain ⟨ep,rp,lp,prodRun,prodRep⟩ := product_return x y px py n1 rt rt dense1
            ⟨ax,byp,rt,rt⟩ 145 frames source
          let h2 := h1++ep
          let n2 := n1+ep.length
          let e2 : NaturalHeap := [.pair rp rt]
          let h3 := h2++e2
          have pair0 : h1[next]?=some (.pair a b) := by
            apply lookup_extend (h:=h0)
            simp [h0,e0,hn]
          have hx0 : h0[a]?=some (.pair ax tx) := lookup_extend hx e0
          have hy0 : h0[b]?=some (.pair byp ty) := lookup_extend hy e0
          have hx1 : h1[a]?=some (.pair ax tx) := lookup_extend (lookup_extend hx e0) et
          have hy1 : h1[b]?=some (.pair byp ty) := lookup_extend (lookup_extend hy e0) et
          have t132 : tickNatural program (state heap next a b c d frames source 132)=
              some ⟨state heap next a b c d frames source 135,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,hx,tagBranch]
          have t135 : tickNatural program (state heap next a b c d frames source 135)=
              some ⟨state h0 n0 a b next d frames source 136,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,Registers.set,Recipe.cell,allocateNatural,h0,e0,n0]
          have t136 : tickNatural program (state h0 n0 a b next d frames source 136)=
              some ⟨state h0 n0 tx b next d frames source 137,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,Registers.set,hx0]
          have t137 : tickNatural program (state h0 n0 tx b next d frames source 137)=
              some ⟨state h0 n0 tx ty next d frames source 138,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,Registers.set,hy0]
          have t138 : tickNatural program (state h0 n0 tx ty next d frames source 138)=
              some ⟨state h0 n0 tx ty next d (⟨139,.r3,⟨tx,ty,next,d⟩⟩::frames) source 132,[],0⟩ := by
            simp [tickNatural,program,state]
          have t139 : tickNatural program (state h1 n1 tx ty next rt frames source 139)=
              some ⟨state h1 n1 a ty next rt frames source 140,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,Registers.set,pair0]
          have t140 : tickNatural program (state h1 n1 a ty next rt frames source 140)=
              some ⟨state h1 n1 a b next rt frames source 141,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,Registers.set,pair0]
          have t141 : tickNatural program (state h1 n1 a b next rt frames source 141)=
              some ⟨state h1 n1 ax b next rt frames source 142,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,Registers.set,hx1]
          have t142 : tickNatural program (state h1 n1 ax b next rt frames source 142)=
              some ⟨state h1 n1 ax byp next rt frames source 143,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,Registers.set,hy1]
          have t143 : tickNatural program (state h1 n1 ax byp next rt frames source 143)=
              some ⟨state h1 n1 ax byp rt rt frames source 144,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,Registers.set]
          have t144 : tickNatural program (state h1 n1 ax byp rt rt frames source 144)=
              some ⟨state h1 n1 ax byp rt rt (⟨145,.r3,⟨ax,byp,rt,rt⟩⟩::frames) source 130,[],0⟩ := by
            simp [tickNatural,program,state]
          have t145 : tickNatural program (state h2 n2 ax byp rt rp frames source 145)=
              some ⟨state h3 (n2+1) ax byp rt n2 frames source 146,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,Registers.set,Recipe.cell,allocateNatural,h3,e2]
          have t146 : tickNatural program (state h3 (n2+1) ax byp rt n2 frames source 146)=
              some ⟨state h3 (n2+1) saved.a saved.b saved.c n2 stack source pc,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,Registers.set,frames]
          have whole := NaturalRun.step t132 (.step t135 (.step t136 (.step t137 (.step t138
            (run_append tailRun (.step t139 (.step t140 (.step t141 (.step t142 (.step t143 (.step t144
              (run_append prodRun (.step t145 (.step t146 (.done _)))))))))))))))
          let ext := e0++et++ep++e2
          have eh : heap++ext=h3 := by simp [ext,h3,h2,h1,h0,List.append_assoc]
          have en : next+ext.length=n2+1 := by simp [ext,e0,e2,n2,n1,n0];omega
          refine ⟨ext,n2,by simp [ext,e0,e2,cells,lt,lp];omega,?_,?_⟩
          · rw [eh,en]
            convert whole using 1 <;> simp [steps]
            omega
          · rw [eh]
            apply StoredList.cons (head:=rp) (tail:=rt)
            · have dense2 : n2=h2.length := by simp [n2,h2,dense1]
              simp [h3,e2,dense2]
            · exact stored_extend prodRep e2
            · exact list_extend (list_extend tailRep ep) e2
end DirectedFlowCutGap.ObjectiveProductList
