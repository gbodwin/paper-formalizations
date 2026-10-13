import DirectedFlowCutGap.GridInputTrace

namespace DirectedFlowCutGap.GridInputProgram
open BinaryArithmetic BinaryRational

theorem dimension_length (rows : List Fraction) : (dimension rows).length ≤ rows.length := by
  simpa only [dimension,List.length_nil,Nat.zero_add] using (BinaryLengthProgram.countWord_spec rows.length []).2

def inputSteps (rows : List Fraction) : ℕ := InputWidthProgram.inputSteps rows+
  (8*rows.length+12)*rows.length+900*(rows.length+InputWidthProgram.bits rows+15)^2+30

theorem steps_bound (rows : List Fraction) : steps rows+1 ≤ inputSteps rows := by
  have hw := InputWidthProgram.steps_bound rows
  have hl := BinaryLengthProgram.scanSteps_bound rows.length []
  simp only [List.length_nil,Nat.zero_add] at hl
  have hd := dimension_length rows
  have hb := InputWidthProgram.width_length rows
  have hf : GridFuelProgram.steps (dimension rows) (width rows)+1 ≤
      900*(rows.length+InputWidthProgram.bits rows+15)^2 := by
    apply (GridFuelProgram.steps_bound (dimension rows) (width rows)).trans
    unfold GridFuelProgram.inputSteps
    apply Nat.mul_le_mul_left 900
    apply Nat.pow_le_pow_left
    dsimp only [width]
    omega
  unfold steps inputSteps InputWidthProgram.inputSteps
  omega
end DirectedFlowCutGap.GridInputProgram
