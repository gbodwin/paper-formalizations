import DirectedFlowCutGap.NaturalFractionProgram

namespace DirectedFlowCutGap.NaturalFractionProgram
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead
open RationalComparisonProgram

theorem fraction {heap : NaturalHeap} {word : Bits} {a : ℕ}
    (input : BoolList heap a word) (next b c d : ℕ) (dense : next=heap.length)
    (stack : List (Frame ℕ 8)) (source : Bits) :
    ∃ ext root,ext.length=4 ∧
      NaturalRun program 6 (state heap next a b c d stack source 6) []
        (state (heap++ext) (next+ext.length) a b c root stack source 7) ∧
      Stored (heap++ext) root (BinaryFractionalCore.naturalFraction word) := by
  obtain ⟨body,rep⟩ := fraction_return input next b c d dense ⟨a,b,c,d⟩ 7 stack source
  have tick : tickNatural program (state heap next a b c d stack source 6)=
      some ⟨state heap next a b c d (⟨7,.r3,⟨a,b,c,d⟩⟩::stack) source 0,[],0⟩ := by rfl
  refine ⟨extension next a,next+3,by simp [extension],?_,rep⟩
  simpa [extension] using NaturalRun.step tick body
end DirectedFlowCutGap.NaturalFractionProgram
