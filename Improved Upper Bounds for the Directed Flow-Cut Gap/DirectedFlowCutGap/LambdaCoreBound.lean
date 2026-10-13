import DirectedFlowCutGap.LambdaCoreTrace

namespace DirectedFlowCutGap.LambdaCoreProgram
open BinaryArithmetic BinaryRational BinaryFractionalRows

/-- Original padded field lengths and numerical exponent. The power output
itself has numerical-exponent-plus-one bits; no binary-length-only claim. -/
def inputSize (x : Fraction) (dimension exponent : Bits) : ℕ :=
  x.num.length+x.den.length+dimension.length+exponent.length+value exponent+4
def inputSteps (x : Fraction) (dimension exponent : Bits) : ℕ :=
  50000*(inputSize x dimension exponent)^2

theorem original_widths (x : Fraction) (dimension exponent : Bits) :
    let L:=inputSize x dimension exponent
    StoredBounded x L ∧ StoredBounded (BinaryFractionalCore.naturalFraction dimension) L ∧
    StoredBounded (quotient x dimension) (2*L+1) ∧ (power exponent).length ≤ L := by
  dsimp only
  have hx : StoredBounded x (inputSize x dimension exponent) := by
    constructor <;> unfold inputSize <;> omega
  have hd : StoredBounded (BinaryFractionalCore.naturalFraction dimension) (inputSize x dimension exponent) := by
    constructor
    · simp only [BinaryFractionalCore.naturalFraction];unfold inputSize;omega
    · simp only [BinaryFractionalCore.naturalFraction,List.length_cons,List.length_nil];unfold inputSize;omega
  have hq := div_stored_bounded (stored_raw_bound hx) (stored_raw_bound hd)
  have hp := (BinaryCounters.powerOfTwoBinary_spec exponent).2.1
  refine ⟨hx,hd,?_,?_⟩
  · simpa [quotient,two_mul] using hq
  · change (BinaryCounters.powerOfTwoBinary exponent).1.length ≤ _
    rw [hp];unfold inputSize;omega

theorem steps_bound (x : Fraction) (dimension exponent : Bits) :
    steps x dimension exponent+1 ≤ inputSteps x dimension exponent := by
  let L:=inputSize x dimension exponent
  have hl : 4 ≤ L := by dsimp [L,inputSize];omega
  obtain ⟨hx,hd,hq,hp⟩ := original_widths x dimension exponent
  have qs : CanonicalRationalQuotient.inputSize x (BinaryFractionalCore.naturalFraction dimension) ≤ 5*L := by
    unfold CanonicalRationalQuotient.inputSize
    obtain ⟨a,b⟩ := hx;obtain ⟨c,d⟩ := hd
    change _ ≤ 5*inputSize x dimension exponent
    dsimp [L] at hl;omega
  have ps : CanonicalRationalProduct.inputSize (quotient x dimension)
      (BinaryFractionalCore.naturalFraction (power exponent)) ≤ 7*L := by
    unfold CanonicalRationalProduct.inputSize
    obtain ⟨a,b⟩ := hq
    simp only [BinaryFractionalCore.naturalFraction,List.length_cons,List.length_nil]
    dsimp [L] at *;omega
  have qbound := (CanonicalRationalQuotient.steps_bound x (BinaryFractionalCore.naturalFraction dimension)).trans
    (Nat.mul_le_mul_left 600 (Nat.pow_le_pow_left qs 2))
  have mbound := (CanonicalRationalProduct.instructions_bound (quotient x dimension)
      (BinaryFractionalCore.naturalFraction (power exponent))).trans
    (Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left ps 2))
  have ev : value exponent+1 ≤ L := by dsimp [L,inputSize];omega
  have el : exponent.length+1 ≤ L := by dsimp [L,inputSize];omega
  have pb := BinaryPowerProgram.steps_bound exponent
  have pe : BinaryPowerProgram.inputSteps exponent ≤ 64*L^2 := by
    unfold BinaryPowerProgram.inputSteps
    calc
      _ ≤ 64*L*L := Nat.mul_le_mul (Nat.mul_le_mul_left 64 ev) el
      _ = _ := by ring
  have pbound := pb.trans pe
  change _ ≤ 50000*L^2
  unfold steps
  nlinarith
end DirectedFlowCutGap.LambdaCoreProgram
