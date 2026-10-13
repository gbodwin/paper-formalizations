import DirectedFlowCutGap.ScalarAdditionRowProgram

namespace DirectedFlowCutGap.ScalarAdditionRow
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor RationalComparisonProgram

theorem addition_return (x y : Fraction) {heap : NaturalHeap} {a b : ℕ}
    (left : Stored heap a x) (right : Stored heap b y) (next c d : ℕ)
    (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 160)
    (stack : List (Frame ℕ 160)) (source : Bits) :
    ∃ ext root, ext.length=CanonicalRationalAddition.cells x y ∧
      NaturalRun program (CanonicalRationalAddition.instructions x y+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 140) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Stored (heap++ext) root (BinaryRational.add x y).1 := by
  obtain ⟨ext,root,len,core,rep⟩ := CanonicalRationalAddition.add_high x y
    (CanonicalRationalAddition.state heap next a b c d [] source 140) rfl hn left right rfl
  have lift := ReferenceProgramLabels.run label CanonicalRationalAddition.program program slots core
  have lift := ReferenceProgramStack.run program (⟨pc,.r3,saved⟩::stack) lift
  have body : NaturalRun program (1+CanonicalRationalAddition.instructions x y)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 140) []
      (state (heap++ext) (next+ext.length) a b c root (⟨pc,.r3,saved⟩::stack) source 141) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,ReferenceProgramStack.state,
      CanonicalRationalAddition.state,label,state] using lift
  have ret : tickNatural program
      (state (heap++ext) (next+ext.length) a b c root (⟨pc,.r3,saved⟩::stack) source 141)=
      some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  refine ⟨ext,root,len,?_,rep⟩
  convert run_append body (.step ret (.done _)) using 1 <;> simp
  omega

theorem add_head (scalar x : Fraction) {heap : NaturalHeap} {a b : ℕ}
    (head : Stored heap a x) (sc : Stored heap b scalar) (next tail : ℕ)
    (hn : next=heap.length) (stack : List (Frame ℕ 160)) (source : Bits) :
    ∃ ext root,ext.length=CanonicalRationalAddition.cells x scalar ∧
      NaturalRun program (CanonicalRationalAddition.instructions x scalar+3)
        (state heap next a b tail tail stack source 150) []
        (state (heap++ext) (next+ext.length) a b tail root stack source 151) ∧
      Stored (heap++ext) root (BinaryRational.add x scalar).1 := by
  obtain ⟨ext,root,len,body,rep⟩ := addition_return x scalar head sc next tail tail hn
    ⟨a,b,tail,tail⟩ 151 stack source
  have call : tickNatural program (state heap next a b tail tail stack source 150)=
      some ⟨state heap next a b tail tail (⟨151,.r3,⟨a,b,tail,tail⟩⟩::stack) source 140,[],0⟩ := by
    simp [tickNatural,program,state]
  refine ⟨ext,root,len,?_,rep⟩
  convert NaturalRun.step call body using 1
  simp
end DirectedFlowCutGap.ScalarAdditionRow
