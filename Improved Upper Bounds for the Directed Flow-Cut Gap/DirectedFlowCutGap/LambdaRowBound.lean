import DirectedFlowCutGap.LambdaRowTrace

namespace DirectedFlowCutGap.LambdaRowProgram
open BinaryArithmetic BinaryRational

def rowBits : List Fraction → ℕ
  | [] => 0
  | q::qs => q.num.length+q.den.length+rowBits qs

theorem member_bits {rows : List Fraction} {x : Fraction} (mem : x∈rows) :
    x.num.length+x.den.length ≤ rowBits rows := by
  induction rows with
  | nil => simp at mem
  | cons q qs ih =>
    simp only [List.mem_cons] at mem
    rcases mem with rfl|mem
    · simp only [rowBits];omega
    · have h := ih mem
      simp only [rowBits];omega

def inputSize (rows : List Fraction) (index dimension exponent : Bits) : ℕ :=
  rowBits rows+rows.length+index.length+dimension.length+exponent.length+value exponent+5

def inputSteps (rows : List Fraction) (index dimension exponent : Bits) : ℕ :=
  50100*(inputSize rows index dimension exponent)^2

theorem steps_bound (rows : List Fraction) (index dimension exponent : Bits)
    (valid : value index<rows.length) :
    steps rows index dimension exponent+1 ≤ inputSteps rows index dimension exponent := by
  have mem : IndexedRationalRead.lookup rows index∈rows := by
    simpa only [IndexedRationalRead.lookup,List.getElem?_eq_getElem valid,Option.getD_some]
      using List.getElem_mem valid
  have hb := member_bits mem
  have hs : LambdaCoreProgram.inputSize (IndexedRationalRead.lookup rows index) dimension exponent ≤ 
      inputSize rows index dimension exponent := by
    unfold LambdaCoreProgram.inputSize inputSize;omega
  have core := (LambdaCoreProgram.steps_bound (IndexedRationalRead.lookup rows index) dimension exponent).trans
    (Nat.mul_le_mul_left 50000 (Nat.pow_le_pow_left hs 2))
  have readBound := BinaryIndexedPairRead.steps_bound index
  have hl : 5 ≤ inputSize rows index dimension exponent := by unfold inputSize;omega
  have hv : value index ≤ inputSize rows index dimension exponent := by unfold inputSize;omega
  have hi : index.length ≤ inputSize rows index dimension exponent := by unfold inputSize;omega
  unfold steps inputSteps
  nlinarith
end DirectedFlowCutGap.LambdaRowProgram
