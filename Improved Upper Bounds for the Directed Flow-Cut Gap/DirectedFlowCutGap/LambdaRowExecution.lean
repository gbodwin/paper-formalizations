import DirectedFlowCutGap.LambdaRowBound

namespace DirectedFlowCutGap.LambdaRowProgram
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead
open RationalComparisonProgram

theorem compute {heap : NaturalHeap} {rows : List Fraction} {index dimension exponent : Bits}
    {a b c d : ℕ} (table : WordPairTableRead.Table heap a (IndexedRationalRead.fields rows))
    (idx : BoolList heap b index) (dim : BoolList heap c dimension) (exp : BoolList heap d exponent)
    (valid : value index<rows.length) (next : ℕ) (dense : next=heap.length)
    (stack : List (Frame ℕ 480)) (source : Bits) :
    ∃ ext root,ext.length=cells rows index dimension exponent ∧
      NaturalRun program (steps rows index dimension exponent+1)
        (state heap next a b c d stack source 478) []
        (state (heap++ext) (next+ext.length) a b c root stack source 479) ∧
      Stored (heap++ext) root (result rows index dimension exponent) := by
  obtain ⟨ext,root,len,core,rep⟩ := lambda_return table idx dim exp valid next dense ⟨a,b,c,d⟩ 479 stack source
  have first : tickNatural program (state heap next a b c d stack source 478)=
      some ⟨state heap next a b c d (⟨479,.r3,⟨a,b,c,d⟩⟩::stack) source 462,[],0⟩ := by rfl
  exact ⟨ext,root,len,by simpa [Nat.add_comm] using NaturalRun.step first core,rep⟩

theorem result_original {n : ℕ} (row : BinaryFractionalRows.Row n) (j : Fin n)
    (index dimension exponent : Bits) (label : value index=j.val) :
    result row.toList index dimension exponent=(BinaryFractionalGuesses.lambda row j dimension exponent).1 := by
  have readEq : IndexedRationalRead.lookup row.toList index=BinaryFractionalRows.get row j := by
    unfold IndexedRationalRead.lookup
    rw [label]
    simp [BinaryFractionalRows.get,Vector.getElem_toList,j.isLt]
  simp only [result,readEq,← BinaryFractionalGraphOracle.read_value row j]
  exact LambdaCoreProgram.result_original row j dimension exponent
end DirectedFlowCutGap.LambdaRowProgram
