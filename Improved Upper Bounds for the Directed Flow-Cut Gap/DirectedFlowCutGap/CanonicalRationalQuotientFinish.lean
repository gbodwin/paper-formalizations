import DirectedFlowCutGap.CanonicalRationalQuotientPrefix

namespace DirectedFlowCutGap.CanonicalRationalQuotient
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor RationalComparisonProgram

theorem nonzero_finish (x y : Fraction) (hy : (BinaryArithmetic.isZero y.num).1=false)
    {heap : NaturalHeap} {a b c d ax byp : ℕ}
    (flag : heap[d]?=some (.flag false)) (pair : heap[c]?=some (.pair ax byp))
    (left : Stored heap ax x) (right : Stored heap byp y)
    (next : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 164)
    (stack : List (Frame ℕ 164)) (source : Bits) :
    ∃ ext root,ext.length=crossCells x y+1 ∧
      NaturalRun program (crossSteps x y+10)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 147) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Stored (heap++ext) root (BinaryRational.div x y).1 := by
  obtain ⟨yn,yd,record,num,den⟩ := right
  let frames : List (Frame ℕ 164) := ⟨pc,.r3,saved⟩::stack
  let e0 : NaturalHeap := [.pair yd yn]
  let h0 := heap++e0
  let n0 := next+1
  have dense0 : n0=h0.length := by simp [n0,h0,e0,hn]
  have inverse : Stored h0 next (reciprocal y hy) := by
    refine ⟨yd,yn,?_,boolList_extend den e0,boolList_extend num e0⟩
    simp [h0,e0,hn]
  obtain ⟨ep,rp,lp,prodRun,prodRep⟩ := product_return x (reciprocal y hy)
    (stored_extend left e0) inverse n0 yn d dense0 ⟨ax,next,yn,d⟩ 159 frames source
  let h1 := h0++ep
  let n1 := n0+ep.length
  have t147 : tickNatural program (state heap next a b c d frames source 147)=
      some ⟨state heap next a b c d frames source 153,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,flag,tagBranch]
  have t153 : tickNatural program (state heap next a b c d frames source 153)=
      some ⟨state heap next ax b c d frames source 154,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,pair]
  have t154 : tickNatural program (state heap next ax b c d frames source 154)=
      some ⟨state heap next ax byp c d frames source 155,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,pair]
  have t155 : tickNatural program (state heap next ax byp c d frames source 155)=
      some ⟨state heap next ax byp yn d frames source 156,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,record]
  have t156 : tickNatural program (state heap next ax byp yn d frames source 156)=
      some ⟨state heap next ax yd yn d frames source 157,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,record]
  have t157 : tickNatural program (state heap next ax yd yn d frames source 157)=
      some ⟨state h0 n0 ax next yn d frames source 158,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,Recipe.cell,allocateNatural,h0,e0,n0]
  have t158 : tickNatural program (state h0 n0 ax next yn d frames source 158)=
      some ⟨state h0 n0 ax next yn d (⟨159,.r3,⟨ax,next,yn,d⟩⟩::frames) source 130,[],0⟩ := by
    simp [tickNatural,program,state]
  have t159 : tickNatural program (state h1 n1 ax next yn rp frames source 159)=
      some ⟨state h1 n1 saved.a saved.b saved.c rp stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,frames]
  have whole := NaturalRun.step t147 (.step t153 (.step t154 (.step t155 (.step t156
    (.step t157 (.step t158 (run_append prodRun (.step t159 (.done _)))))))))
  refine ⟨e0++ep,rp,?_,?_,?_⟩
  · simp [e0,lp,crossCells,CanonicalRationalProduct.cells,reciprocal,Nat.add_comm]
  · convert whole using 1 <;> simp [crossSteps,CanonicalRationalProduct.instructions,reciprocal,
      h1,h0,n1,n0,e0,List.append_assoc,Nat.add_assoc]
    simp [Nat.add_comm]
  · rw [←nonzero_exact x y hy]
    simpa [List.append_assoc] using prodRep
end DirectedFlowCutGap.CanonicalRationalQuotient
