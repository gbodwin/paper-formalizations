import DirectedFlowCutGap.ShiftedGridTrace

namespace DirectedFlowCutGap.ShiftedGridProgram
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead
open RationalComparisonProgram CanonicalRationalSum

theorem compute {heap : NaturalHeap} {rows : List Fraction} {index exponent : Bits}
    {a b c : ℕ} (table : WordPairTableRead.Table heap a (IndexedRationalRead.fields rows))
    (idx : BoolList heap b index) (exp : BoolList heap c exponent)
    (valid : value index<rows.length) (next d : ℕ) (dense : next=heap.length)
    (stack : List (Frame ℕ 1220)) (source : Bits) :
    ∃ ext root,ext.length=cells rows index exponent ∧
      NaturalRun program (steps rows index exponent+1)
        (state heap next a b c d stack source 1218) []
        (state (heap++ext) (next+ext.length) a b c root stack source 1219) ∧
      StoredList (heap++ext) root (result rows index exponent) := by
  obtain ⟨ext,root,len,core,rep⟩ := shifted_return table idx exp valid next d dense
    ⟨a,b,c,d⟩ 1219 stack source
  have first : tickNatural program (state heap next a b c d stack source 1218)=
      some ⟨state heap next a b c d (⟨1219,.r3,⟨a,b,c,d⟩⟩::stack) source 1200,[],0⟩ := by rfl
  exact ⟨ext,root,len,by simpa [Nat.add_comm] using NaturalRun.step first core,rep⟩

theorem result_original {n : ℕ} (row : BinaryFractionalRows.Row n) (j : Fin n)
    (index exponent : Bits) (label : value index=j.val) :
    result row.toList index exponent=(BinaryFractionalGuesses.shifted row
      (BinaryFractionalGuesses.lambda row j (BinaryFractionalCore.dimension row).1 exponent).1).1.toList := by
  unfold result scalar
  rw [LambdaGridProgram.result_original row j index exponent label]
  exact ScalarAdditionRow.result_eq_shifted row _
end DirectedFlowCutGap.ShiftedGridProgram
