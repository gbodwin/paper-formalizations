import DirectedFlowCutGap.ActualLambdaGrid

namespace DirectedFlowCutGap.LambdaGridProgram
open BinaryArithmetic BinaryRational

/-- This is the numeric range returned by the actual original-row grid prefix.
The later grid loop must still establish its exponent invariant. -/
def gridLimit (rows : List Fraction) : ℕ :=
  value (BinaryFractionalGuesses.gridFuel (GridInputProgram.dimension rows) (GridInputProgram.width rows)).1

theorem width_value_bound (rows : List Fraction) :
    value (GridInputProgram.width rows) ≤ LambdaRowProgram.rowBits rows := by
  induction rows with
  | nil => simp [GridInputProgram.width,BinaryFractionalGuesses.widthList,value,LambdaRowProgram.rowBits]
  | cons q qs ih =>
    have hn : Nat.size (value q.num) ≤ q.num.length := Nat.size_le.mpr (value_lt q.num)
    have hd : Nat.size (value q.den) ≤ q.den.length := Nat.size_le.mpr (value_lt q.den)
    simp only [GridInputProgram.width,BinaryFractionalGuesses.widthList,
      BinaryFractionalGuesses.maximum_value,BinaryFractionalGuesses.fractionWidth_value,
      BinaryRational.decode,LambdaRowProgram.rowBits]
    dsimp only [GridInputProgram.width] at ih
    exact max_le (max_le (by omega) (by omega)) (by omega)

theorem gridLimit_bound (rows : List Fraction) :
    gridLimit rows ≤ 2*LambdaRowProgram.rowBits rows+2*rows.length+3 := by
  have dim : value (GridInputProgram.dimension rows)=rows.length := by
    simpa [GridInputProgram.dimension,value] using (BinaryLengthProgram.countWord_spec rows.length []).1
  have wid := width_value_bound rows
  have ns : Nat.size rows.length ≤ rows.length := Nat.size_le.mpr Nat.lt_two_pow_self
  unfold gridLimit
  rw [BinaryFractionalGuesses.gridFuel_value,dim]
  unfold FractionalCoverGuesses.gridSteps
  omega

/-- An original-bit envelope under the actual original grid-range invariant.
No unrestricted bit-length bound for arbitrary exponent values is asserted. -/
def gridInputSteps (rows : List Fraction) (index exponent : Bits) : ℕ :=
  GridInputProgram.inputSteps rows+
    50100*(3*LambdaRowProgram.rowBits rows+4*rows.length+index.length+exponent.length+8)^2+12

theorem inputSteps_le_grid (rows : List Fraction) (index exponent : Bits)
    (range : value exponent ≤ gridLimit rows) :
    inputSteps rows index exponent ≤ gridInputSteps rows index exponent := by
  have lim := gridLimit_bound rows
  have size : inputSize rows index exponent ≤
      3*LambdaRowProgram.rowBits rows+4*rows.length+index.length+exponent.length+8 := by
    unfold inputSize;omega
  unfold inputSteps gridInputSteps
  exact Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left 50100
    (Nat.pow_le_pow_left size 2)) (GridInputProgram.inputSteps rows)) 12

theorem grid_steps_bound (rows : List Fraction) (index exponent : Bits)
    (valid : value index<rows.length) (range : value exponent ≤ gridLimit rows) :
    steps rows index exponent+1 ≤ gridInputSteps rows index exponent :=
  (steps_bound rows index exponent valid).trans (inputSteps_le_grid rows index exponent range)

open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead RationalComparisonProgram

theorem lambda_grid_bit {H A : ℕ} {rows : List Fraction} {index exponent : Bits}
    (initial : BitState 1040) (bounded : initial.Bounded H A) (pc0 : initial.pc=1038)
    (dense : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (table : WordPairTableRead.Table (eraseState initial).heap (eraseState initial).registers.a (IndexedRationalRead.fields rows))
    (idx : BoolList (eraseState initial).heap (eraseState initial).registers.b index)
    (exp : BoolList (eraseState initial).heap (eraseState initial).registers.c exponent)
    (valid : value index<rows.length) (range : value exponent ≤ gridLimit rows) :
    ∃ charge out,Run program (steps rows index exponent+1) charge initial [] out ∧
      Stored (eraseState out).heap (eraseState out).registers.d (result rows index exponent) ∧
      out.source=initial.source ∧ (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 1040 H A (gridInputSteps rows index exponent) := by
  obtain ⟨charge,out,run,rep,_,_,_,source,_,_,_,stop,paid⟩ :=
    lambda_bit initial bounded pc0 dense empty table idx exp valid
  exact ⟨charge,out,run,rep,source,stop,paid.trans
    (SupportSearchEncoding.complete_mono 1040 H A _ _ (inputSteps_le_grid rows index exponent range))⟩
end DirectedFlowCutGap.LambdaGridProgram
