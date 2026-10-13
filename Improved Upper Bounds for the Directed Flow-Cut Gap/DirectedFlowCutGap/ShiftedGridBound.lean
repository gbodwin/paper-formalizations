import DirectedFlowCutGap.ShiftedGridExecution

namespace DirectedFlowCutGap.ShiftedGridProgram
open BinaryArithmetic BinaryRational

def scalarWidth (rows : List Fraction) (exponent : Bits) : ℕ :=
  LambdaRowProgram.rowBits rows+(rows.length+1)+1+(value exponent+1)+1

theorem scalar_width (rows : List Fraction) (index exponent : Bits)
    (valid : value index<rows.length) : StoredBounded (scalar rows index exponent) (scalarWidth rows exponent) := by
  have mem : IndexedRationalRead.lookup rows index∈rows := by
    simpa only [IndexedRationalRead.lookup,List.getElem?_eq_getElem valid,Option.getD_some]
      using List.getElem_mem valid
  have hb := LambdaRowProgram.member_bits mem
  have xb : StoredBounded (IndexedRationalRead.lookup rows index) (LambdaRowProgram.rowBits rows) :=
    ⟨by omega,by omega⟩
  have dim : StoredBounded (BinaryFractionalCore.naturalFraction (GridInputProgram.dimension rows))
      (rows.length+1) := by
    constructor
    · exact (GridInputProgram.dimension_length rows).trans (by omega)
    · change 1 ≤ rows.length+1;omega
  have qb := div_stored_bounded (BinaryFractionalRows.stored_raw_bound xb)
    (BinaryFractionalRows.stored_raw_bound dim)
  have pw : StoredBounded (BinaryFractionalCore.naturalFraction (LambdaCoreProgram.power exponent))
      (value exponent+1) := by
    constructor
    · exact le_of_eq (BinaryCounters.powerOfTwoBinary_spec exponent).2.1
    · change 1 ≤ value exponent+1;omega
  exact mul_stored_bounded (BinaryFractionalRows.stored_raw_bound qb)
    (BinaryFractionalRows.stored_raw_bound pw)

theorem rowBits_same (rows : List Fraction) : ScalarAdditionRow.rowBits rows=LambdaRowProgram.rowBits rows := by
  induction rows with
  | nil => rfl
  | cons x xs ih => simp only [ScalarAdditionRow.rowBits,LambdaRowProgram.rowBits,ih]

def inputSteps (rows : List Fraction) (index exponent : Bits) : ℕ :=
  LambdaGridProgram.inputSteps rows index exponent+
    ScalarAdditionRow.instructionBound rows.length (LambdaRowProgram.rowBits rows+2*scalarWidth rows exponent)+8

theorem steps_bound (rows : List Fraction) (index exponent : Bits) (valid : value index<rows.length) :
    steps rows index exponent+1 ≤ inputSteps rows index exponent := by
  obtain ⟨sn,sd⟩ := scalar_width rows index exponent valid
  have hsc : (scalar rows index exponent).num.length+(scalar rows index exponent).den.length ≤
      LambdaRowProgram.rowBits rows+2*scalarWidth rows exponent := by omega
  have add := ScalarAdditionRow.steps_bound (scalar rows index exponent) rows _ hsc
    (fun x hx => (LambdaRowProgram.member_bits hx).trans (by omega))
  have grid := LambdaGridProgram.steps_bound rows index exponent valid
  unfold steps inputSteps
  omega

def gridInputSteps (rows : List Fraction) (index exponent : Bits) : ℕ :=
  LambdaGridProgram.gridInputSteps rows index exponent+
    ScalarAdditionRow.instructionBound rows.length
      (LambdaRowProgram.rowBits rows+2*(3*LambdaRowProgram.rowBits rows+3*rows.length+7))+8

theorem inputSteps_le_grid (rows : List Fraction) (index exponent : Bits)
    (range : value exponent ≤ LambdaGridProgram.gridLimit rows) :
    inputSteps rows index exponent ≤ gridInputSteps rows index exponent := by
  have gl := LambdaGridProgram.inputSteps_le_grid rows index exponent range
  have lim := LambdaGridProgram.gridLimit_bound rows
  have sw : scalarWidth rows exponent ≤ 3*LambdaRowProgram.rowBits rows+3*rows.length+7 := by
    unfold scalarWidth;omega
  unfold inputSteps gridInputSteps ScalarAdditionRow.instructionBound
  gcongr
end DirectedFlowCutGap.ShiftedGridProgram
