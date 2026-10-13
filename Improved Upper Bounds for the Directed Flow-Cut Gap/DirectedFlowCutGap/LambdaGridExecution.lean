import DirectedFlowCutGap.LambdaGridBound

namespace DirectedFlowCutGap.LambdaGridProgram
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead
open RationalComparisonProgram

theorem compute {heap : NaturalHeap} {rows : List Fraction} {index exponent : Bits}
    {a b c : ℕ} (table : WordPairTableRead.Table heap a (IndexedRationalRead.fields rows))
    (idx : BoolList heap b index) (exp : BoolList heap c exponent)
    (valid : value index<rows.length) (next d : ℕ) (dense : next=heap.length)
    (stack : List (Frame ℕ 1040)) (source : Bits) :
    ∃ ext root,ext.length=cells rows index exponent ∧
      NaturalRun program (steps rows index exponent+1)
        (state heap next a b c d stack source 1038) []
        (state (heap++ext) (next+ext.length) a b c root stack source 1039) ∧
      Stored (heap++ext) root (result rows index exponent) := by
  obtain ⟨ext,root,len,core,rep⟩ := lambda_return table idx exp valid next d dense ⟨a,b,c,d⟩ 1039 stack source
  have first : tickNatural program (state heap next a b c d stack source 1038)=
      some ⟨state heap next a b c d (⟨1039,.r3,⟨a,b,c,d⟩⟩::stack) source 1024,[],0⟩ := by rfl
  exact ⟨ext,root,len,by simpa [Nat.add_comm] using NaturalRun.step first core,rep⟩

theorem result_original {n : ℕ} (row : BinaryFractionalRows.Row n) (j : Fin n)
    (index exponent : Bits) (label : value index=j.val) :
    result row.toList index exponent=(BinaryFractionalGuesses.lambda row j
      (BinaryFractionalCore.dimension row).1 exponent).1 := by
  rw [result,LambdaRowProgram.result_original row j _ _ _ label,GridInputProgram.dimension_exact]
end DirectedFlowCutGap.LambdaGridProgram
