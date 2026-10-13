import DirectedFlowCutGap.LambdaCoreBound

namespace DirectedFlowCutGap.LambdaCoreProgram
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead
open RationalComparisonProgram

theorem compute {heap : NaturalHeap} {x : Fraction} {dimension exponent : Bits}
    {a b c : ℕ} (cost : Stored heap a x) (dim : BoolList heap b dimension)
    (exp : BoolList heap c exponent) (next d : ℕ) (dense : next=heap.length)
    (stack : List (Frame ℕ 432)) (source : Bits) :
    ∃ ext root,ext.length=cells x dimension exponent ∧
      NaturalRun program (steps x dimension exponent+1)
        (state heap next a b c d stack source 430) []
        (state (heap++ext) (next+ext.length) a b c root stack source 431) ∧
      Stored (heap++ext) root (result x dimension exponent) := by
  obtain ⟨ext,root,len,core,rep⟩ := lambda_return cost dim exp next d dense ⟨a,b,c,d⟩ 431 stack source
  have first : tickNatural program (state heap next a b c d stack source 430)=
      some ⟨state heap next a b c d (⟨431,.r3,⟨a,b,c,d⟩⟩::stack) source 400,[],0⟩ := by rfl
  exact ⟨ext,root,len,by simpa [Nat.add_comm] using NaturalRun.step first core,rep⟩

theorem result_original {n : ℕ} (row : BinaryFractionalRows.Row n) (j : Fin n)
    (dimension exponent : Bits) :
    result (BinaryFractionalGraphOracle.read row j).1 dimension exponent=
      (BinaryFractionalGuesses.lambda row j dimension exponent).1 := by rfl
end DirectedFlowCutGap.LambdaCoreProgram
