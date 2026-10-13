import DirectedFlowCutGap.LambdaCoreCallLift

set_option maxRecDepth 4096

namespace DirectedFlowCutGap.LambdaCoreProgram
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead
open RationalComparisonProgram

theorem natural_call {word : Bits} {heap : NaturalHeap} {a : ℕ}
    (input : BoolList heap a word) (next b c d : ℕ) (dense : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 432) (stack : List (Frame ℕ 432)) (source : Bits) :
    ∃ ext root,ext.length=4 ∧
      NaturalRun program 7 (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 6) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Stored (heap++ext) root (BinaryFractionalCore.naturalFraction word) := by
  obtain ⟨ext,root,len,core,rep⟩ := NaturalFractionProgram.fraction input next b c d dense [] source
  have lift := child_return naturalLabel NaturalFractionProgram.program natural_slots core rfl rfl
    .r3 .r3 saved pc stack (by rfl)
  exact ⟨ext,root,len,by simpa [NaturalFractionProgram.state,naturalLabel,state,Registers.get,Registers.set] using lift,rep⟩

theorem quotient_call (x y : Fraction) {heap : NaturalHeap} {a b : ℕ}
    (left : Stored heap a x) (right : Stored heap b y) (next c d : ℕ) (dense : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 432) (stack : List (Frame ℕ 432)) (source : Bits) :
    ∃ ext root,ext.length=CanonicalRationalQuotient.cells x y ∧
      NaturalRun program (CanonicalRationalQuotient.steps x y+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 169) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Stored (heap++ext) root (BinaryRational.div x y).1 := by
  obtain ⟨ext,root,len,core,rep⟩ := CanonicalRationalQuotient.quotient_high x y
    (CanonicalRationalQuotient.state heap next a b c d [] source 161) rfl dense left right rfl
  have lift := child_return quotientLabel CanonicalRationalQuotient.program quotient_slots core rfl rfl
    .r3 .r3 saved pc stack (by rfl)
  refine ⟨ext,root,len,?_,rep⟩
  convert lift using 1 <;> simp [CanonicalRationalQuotient.state,quotientLabel,state,Registers.get,Registers.set]
  omega

theorem power_call {word : Bits} {heap : NaturalHeap} {a : ℕ}
    (input : BoolList heap a word) (next b c d : ℕ) (dense : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 432) (stack : List (Frame ℕ 432)) (source : Bits) :
    ∃ ext root,ext.length=BinaryPowerProgram.cells word ∧
      NaturalRun program (BinaryPowerProgram.steps word+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 266) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      BoolList (heap++ext) root (power word) := by
  obtain ⟨ext,root,len,core,rep⟩ := BinaryPowerProgram.power input next b c d dense [] source
  have lift := child_return powerLabel BinaryPowerProgram.program power_slots core rfl rfl
    .r3 .r3 saved pc stack (by rfl)
  exact ⟨ext,root,len,by simpa [BinaryPowerProgram.state,powerLabel,state,Registers.get,Registers.set,Nat.add_assoc] using lift,rep⟩

theorem product_call (x y : Fraction) {heap : NaturalHeap} {a b : ℕ}
    (left : Stored heap a x) (right : Stored heap b y) (next c d : ℕ) (dense : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 432) (stack : List (Frame ℕ 432)) (source : Bits) :
    ∃ ext root,ext.length=CanonicalRationalProduct.cells x y ∧
      NaturalRun program (CanonicalRationalProduct.instructions x y+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 398) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Stored (heap++ext) root (BinaryRational.mul x y).1 := by
  obtain ⟨ext,root,len,core,rep⟩ := CanonicalRationalProduct.product_high x y
    (CanonicalRationalProduct.state heap next a b c d [] source 130) rfl dense left right rfl
  have lift := child_return productLabel CanonicalRationalProduct.program product_slots core rfl rfl
    .r3 .r3 saved pc stack (by rfl)
  refine ⟨ext,root,len,?_,rep⟩
  convert lift using 1 <;> simp [CanonicalRationalProduct.state,productLabel,state,Registers.get,Registers.set]
  omega
end DirectedFlowCutGap.LambdaCoreProgram
