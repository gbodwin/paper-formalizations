import DirectedFlowCutGap.LambdaGridTrace

namespace DirectedFlowCutGap.LambdaGridProgram
open BinaryArithmetic BinaryRational

def inputSize (rows : List Fraction) (index exponent : Bits) : ℕ :=
  LambdaRowProgram.rowBits rows+2*rows.length+index.length+exponent.length+value exponent+5

def inputSteps (rows : List Fraction) (index exponent : Bits) : ℕ :=
  GridInputProgram.inputSteps rows+50100*(inputSize rows index exponent)^2+12

theorem steps_bound (rows : List Fraction) (index exponent : Bits) (valid : value index<rows.length) :
    steps rows index exponent+1 ≤ inputSteps rows index exponent := by
  have gd := GridInputProgram.dimension_length rows
  have gs := GridInputProgram.steps_bound rows
  have rs := LambdaRowProgram.steps_bound rows index (GridInputProgram.dimension rows) exponent valid
  have size : LambdaRowProgram.inputSize rows index (GridInputProgram.dimension rows) exponent ≤
      inputSize rows index exponent := by
    unfold LambdaRowProgram.inputSize inputSize;omega
  have bound := rs.trans (Nat.mul_le_mul_left 50100 (Nat.pow_le_pow_left size 2))
  unfold steps inputSteps
  omega
end DirectedFlowCutGap.LambdaGridProgram
