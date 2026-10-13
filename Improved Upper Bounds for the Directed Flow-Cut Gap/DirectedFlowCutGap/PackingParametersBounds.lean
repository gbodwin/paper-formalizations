import DirectedFlowCutGap.PackingParametersExecution

namespace DirectedFlowCutGap.PackingParameters
open BinaryArithmetic BinaryRational BinaryFractionalRows

theorem product_width (xs ys : Bits) : (mulCanonical xs ys).1.length ≤ 2*xs.length+ys.length+1 := by
  exact (trim_spec (mul xs ys).1).2.2.1.trans (mul_spec xs ys).2.1

theorem square_width (n : ℕ) : (squareWord n).length ≤ 3*n+1 := by
  have h := product_width (dimensionWord n) (dimensionWord n)
  have d := dimension_width n
  dsimp only [squareWord]
  omega

theorem fuel_width (n : ℕ) : (fuelWord n).length ≤ 3*n+6 := by
  have h := product_width [true,true] (squareWord n)
  have s := square_width n
  simp only [List.length_cons,List.length_nil] at h
  dsimp only [fuelWord]
  omega

theorem delta_width (n : ℕ) : StoredBounded (deltaValue n) (3*n+9) := by
  have ht : StoredBounded two 2 := by simp [StoredBounded,two]
  have hf : StoredBounded (BinaryFractionalCore.naturalFraction (fuelWord n)) (3*n+6) := by
    constructor
    · exact fuel_width n
    · simp [BinaryFractionalCore.naturalFraction]
  have h := div_stored_bounded (stored_raw_bound ht) (stored_raw_bound hf)
  have he : 2+(3*n+6)+1=3*n+9 := by omega
  rw [he] at h
  exact h

def instructionBound (n : ℕ) : ℕ := 1200*(3*n+12)^2

theorem steps_bound (n : ℕ) : steps n ≤ instructionBound n := by
  have d := dimension_width n
  have s := square_width n
  have f := fuel_width n
  have h1 : (dimensionWord n).length+(dimensionWord n).length+2 ≤ 3*n+12 := by omega
  have h2 : [true,true].length+(squareWord n).length+2 ≤ 3*n+12 := by simp only [List.length_cons,List.length_nil];omega
  have h3 : CanonicalRationalQuotient.inputSize two (BinaryFractionalCore.naturalFraction (fuelWord n)) ≤ 3*n+12 := by
    simp only [CanonicalRationalQuotient.inputSize,two,BinaryFractionalCore.naturalFraction,List.length_cons,List.length_nil]
    omega
  have a := (CanonicalArithmeticProgram.instructions_bound true (dimensionWord n) (dimensionWord n)).trans
    (Nat.mul_le_mul_left 200 (Nat.pow_le_pow_left h1 2))
  have b := (CanonicalArithmeticProgram.instructions_bound true [true,true] (squareWord n)).trans
    (Nat.mul_le_mul_left 200 (Nat.pow_le_pow_left h2 2))
  have c := (CanonicalRationalQuotient.steps_bound two (BinaryFractionalCore.naturalFraction (fuelWord n))).trans
    (Nat.mul_le_mul_left 600 (Nat.pow_le_pow_left h3 2))
  have l := BinaryLengthProgram.scanSteps_bound n []
  simp only [List.length_nil,Nat.zero_add] at l
  dsimp only [steps,instructionBound]
  nlinarith

end DirectedFlowCutGap.PackingParameters
