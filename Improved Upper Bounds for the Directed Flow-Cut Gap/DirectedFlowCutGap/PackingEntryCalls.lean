import DirectedFlowCutGap.PackingEntryProgram
namespace DirectedFlowCutGap.PackingEntry
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram

theorem product_return (x y : Fraction) {heap : NaturalHeap} {a b : ℕ}
    (left : Stored heap a x) (right : Stored heap b y) (next c d : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 480) (stack : List (Frame ℕ 480)) (source : Bits) :
    ∃ ext root,ext.length=CanonicalRationalProduct.cells x y ∧
      NaturalRun program (CanonicalRationalProduct.instructions x y+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 130) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Stored (heap++ext) root (BinaryRational.mul x y).1 := by
  obtain ⟨ext,root,len,high,rep⟩ := CanonicalRationalProduct.product_high x y
    (CanonicalRationalProduct.state heap next a b c d [] source 130) rfl hn left right rfl
  have run := call_run productLabel CanonicalRationalProduct.program product_slots high
    (by simp [program,productLabel,CanonicalRationalProduct.program,callable]) saved pc stack
  refine ⟨ext,root,len,?_,rep⟩
  convert run using 1 <;> simp [state,productLabel,Nat.add_assoc]
  omega

theorem quotient_return (x y : Fraction) {heap : NaturalHeap} {a b : ℕ}
    (left : Stored heap a x) (right : Stored heap b y) (next c d : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 480) (stack : List (Frame ℕ 480)) (source : Bits) :
    ∃ ext root,ext.length=CanonicalRationalQuotient.cells x y ∧
      NaturalRun program (CanonicalRationalQuotient.steps x y+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 293) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Stored (heap++ext) root (BinaryRational.div x y).1 := by
  obtain ⟨ext,root,len,high,rep⟩ := CanonicalRationalQuotient.quotient_high x y
    (CanonicalRationalQuotient.state heap next a b c d [] source 161) rfl hn left right rfl
  have run := call_run quotientLabel CanonicalRationalQuotient.program quotient_slots high
    (by simp [program,quotientLabel,CanonicalRationalQuotient.program,callable]) saved pc stack
  refine ⟨ext,root,len,?_,rep⟩
  convert run using 1 <;> simp [state,quotientLabel,Nat.add_assoc]
  omega

theorem addition_return (x y : Fraction) {heap : NaturalHeap} {a b : ℕ}
    (left : Stored heap a x) (right : Stored heap b y) (next c d : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 480) (stack : List (Frame ℕ 480)) (source : Bits) :
    ∃ ext root,ext.length=CanonicalRationalAddition.cells x y ∧
      NaturalRun program (CanonicalRationalAddition.instructions x y+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 436) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Stored (heap++ext) root (BinaryRational.add x y).1 := by
  obtain ⟨ext,root,len,high,rep⟩ := CanonicalRationalAddition.add_high x y
    (CanonicalRationalAddition.state heap next a b c d [] source 140) rfl hn left right rfl
  have run := call_run additionLabel CanonicalRationalAddition.program addition_slots high
    (by simp [program,additionLabel,CanonicalRationalAddition.program,callable]) saved pc stack
  refine ⟨ext,root,len,?_,rep⟩
  convert run using 1 <;> simp [state,additionLabel,Nat.add_assoc]
  omega

end DirectedFlowCutGap.PackingEntry
