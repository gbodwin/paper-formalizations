import DirectedFlowCutGap.PackingParametersArithmeticCall

namespace DirectedFlowCutGap.PackingParameters
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation PackedBooleanConstructor
open RationalComparisonProgram (Stored)

theorem quotient_return (x y : Fraction) {heap : NaturalHeap} {a b : ℕ}
    (left : Stored heap a x) (right : Stored heap b y) (next c d : ℕ) (dense : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 360) (stack : List (Frame ℕ 360)) (source : Bits) :
    ∃ ext root,
      NaturalRun program (CanonicalRationalQuotient.steps x y+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 301) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Stored (heap++ext) root (BinaryRational.div x y).1 := by
  obtain ⟨ext,root,_,run,rep⟩ := CanonicalRationalQuotient.quotient_high x y
    (CanonicalRationalQuotient.state heap next a b c d [] source 161) rfl dense left right rfl
  have terminal : CanonicalRationalQuotient.program 162=.halt := rfl
  have lifted := child_return quotientLabel CanonicalRationalQuotient.program quotient_slots run rfl rfl
    .r3 .r3 saved pc stack (quotient_halt 162 terminal)
  have entry : quotientLabel 161=(301 : Fin 360) := by decide
  have hc : 1+CanonicalRationalQuotient.steps x y+1=CanonicalRationalQuotient.steps x y+2 := by omega
  rw [hc] at lifted
  exact ⟨ext,root,by simpa only [CanonicalRationalQuotient.state,entry,state,Registers.get,Registers.set] using lifted,rep⟩
end DirectedFlowCutGap.PackingParameters
