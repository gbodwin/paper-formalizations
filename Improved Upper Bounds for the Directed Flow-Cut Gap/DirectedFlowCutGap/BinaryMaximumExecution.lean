import DirectedFlowCutGap.BinaryMaximumTrace

namespace DirectedFlowCutGap.BinaryMaximumProgram
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead

def inputSteps (xs ys : Bits) : ℕ := 24*(xs.length+ys.length+1)

theorem steps_bound (xs ys : Bits) : steps xs ys+1 ≤ inputSteps xs ys := by
  have h := BinaryComparisonProgram.steps_bound xs ys
  unfold steps inputSteps
  omega

theorem maximum {xs ys : Bits} {heap : NaturalHeap} {a b : ℕ}
    (left : BoolList heap a xs) (right : BoolList heap b ys)
    (next c d : ℕ) (hn : next=heap.length) (stack : List (Frame ℕ 56)) (source : Bits) :
    ∃ ext,ext.length=BinaryComparisonProgram.cells xs ys+1 ∧
      NaturalRun program (steps xs ys+1) (state heap next a b c d stack source 54) []
        (state (heap++ext) (next+ext.length) a b c (pointer xs ys a b) stack source 55) ∧
      BoolList (heap++ext) (pointer xs ys a b) (BinaryFractionalGuesses.maximum xs ys).1 := by
  obtain ⟨ext,len,core,rep⟩ := maximum_return left right next c d hn ⟨a,b,c,d⟩ 55 stack source
  have first : tickNatural program (state heap next a b c d stack source 54)=
      some ⟨state heap next a b c d (⟨55,.r3,⟨a,b,c,d⟩⟩::stack) source 48,[],0⟩ := by rfl
  exact ⟨ext,len,by simpa [Nat.add_comm] using NaturalRun.step first core,rep⟩
end DirectedFlowCutGap.BinaryMaximumProgram
