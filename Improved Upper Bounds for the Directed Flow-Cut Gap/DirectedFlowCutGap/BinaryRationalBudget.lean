import DirectedFlowCutGap.BinaryRational
import DirectedFlowCutGap.BinaryDivision
import DirectedFlowCutGap.BinaryFractionalRows
import DirectedFlowCutGap.BinaryNaturalView

namespace DirectedFlowCutGap.BinaryRational

open scoped NNRat
open BinaryArithmetic

/-- Subtract an unsigned integer from a nonnegative fraction, saturating at zero.
The denominator is retained literally. -/
def subtractNat (a : Fraction) (k : Bits) : Fraction × ℕ :=
  let multiplied := mulCanonical k a.den
  let difference := BinaryDivision.sub a.num multiplied.1
  (⟨difference.1,a.den,a.den_pos⟩,multiplied.2+difference.2+5)

theorem subtractNat_value (a : Fraction) (k : Bits) :
    (decode (subtractNat a k).1).value = (decode a).value - (value k : ℚ≥0) := by
  have product := (canonical_values k a.den).2.1
  have subtract := (BinaryDivision.sub_spec a.num (mulCanonical k a.den).1).1
  have nonzero : (value a.den : ℚ≥0) ≠ 0 := by exact_mod_cast a.den_pos.ne'
  change (value (BinaryDivision.sub a.num (mulCanonical k a.den).1).1 : ℚ≥0) / (value a.den : ℚ≥0) =
    (value a.num : ℚ≥0) / (value a.den : ℚ≥0) - (value k : ℚ≥0)
  rw [subtract,product,Nat.cast_tsub,Nat.cast_mul,tsub_div,mul_div_cancel_right₀ _ nonzero]

theorem subtractNat_stored (a : Fraction) (k : Bits) {B : ℕ} (fits : StoredBounded a B) :
    StoredBounded (subtractNat a k).1 B := by
  change (BinaryDivision.sub a.num (mulCanonical k a.den).1).1.length ≤ B ∧ a.den.length ≤ B
  refine ⟨?_,fits.2⟩
  rw [(BinaryDivision.sub_spec a.num (mulCanonical k a.den).1).2.1]
  exact (Nat.size_le_size (Nat.sub_le ..)).trans ((Nat.size_le.mpr (value_lt a.num)).trans fits.1)

theorem subtractNat_paid (a : Fraction) (k : Bits) {B : ℕ} (fits : StoredBounded a B)
    (fitsK : k.length ≤ B) :
    (subtractNat a k).2 ≤ 512*(B+1)^2+64*(4*B+2)+5 := by
  have hm := (canonical_charges fitsK fits.2).2
  have hproduct : (mulCanonical k a.den).1.length ≤ 3*B+1 := by
    have trimLength := (trim_spec (BinaryArithmetic.mul k a.den).1).2.2.1
    have productLength := (mul_spec k a.den).2.1
    change (trim (BinaryArithmetic.mul k a.den).1).1.length ≤ _
    have fitDen := fits.2
    omega
  have hs := (BinaryDivision.sub_spec a.num (mulCanonical k a.den).1).2.2
  have fitNum := fits.1
  unfold subtractNat
  dsimp only
  omega

private def two : Fraction := ⟨[false,true],[true],by decide⟩

private theorem two_value : (decode two).value = 2 := by
  change (2 : ℚ≥0) / 1 = 2
  simp

private theorem smallConstants (k : ℕ) : StoredBounded one (2*k+2) ∧ StoredBounded two (2*k+2) := by
  simp only [StoredBounded,one,two,List.length_cons,List.length_nil]
  omega

/-- Encode the reciprocal of twice the typed vertex count. -/
def halfDimension (n : ℕ) : Fraction × ℕ :=
  if h : n = 0 then (zero,2) else
    let bits := BinaryNaturalView.encode n
    (⟨[true],false::bits.1,by
      change 0 < 0 + 2 * value bits.1
      rw [BinaryNaturalView.encode_value]
      omega⟩,bits.2+6)

theorem halfDimension_value (n : ℕ) :
    (decode (halfDimension n).1).value = (2 * (n : ℚ≥0))⁻¹ := by
  unfold halfDimension
  split
  · rename_i zeroSize
    subst n
    simp
  · change (1 : ℚ≥0) / ((0 + 2 * value (BinaryNaturalView.encode n).1 : ℕ) : ℚ≥0) = _
    rw [BinaryNaturalView.encode_value]
    simp [one_div]

theorem halfDimension_stored (n : ℕ) : StoredBounded (halfDimension n).1 (n.size+2) := by
  unfold halfDimension
  split
  · simp [StoredBounded,zero]
  · simp [StoredBounded,BinaryNaturalView.encode_bits,Nat.size_eq_bits_len]

theorem halfDimension_paid (n : ℕ) : (halfDimension n).2 ≤ 16*(n.size+1)^2+6 := by
  have paid := BinaryNaturalView.encode_paid n
  unfold halfDimension
  split <;> dsimp only <;> omega

/-- Spend the available budget on subunit lengths, with multiplier capped at two. -/
def budgetGain (total : Fraction) (reserved : Bits) (subunit : Fraction) : Fraction × ℕ :=
  let empty := isZero subunit
  if empty.1 then (one,empty.2+4) else
    let available := subtractNat total reserved
    let ratio := BinaryRational.div available.1 subunit
    let cap := BinaryRational.le ratio.1 two
    (if cap.1 then ratio.1 else two,empty.2+available.2+ratio.2+cap.2+8)

theorem budgetGain_value (total : Fraction) (reserved : Bits) (subunit : Fraction) :
    (decode (budgetGain total reserved subunit).1).value =
      if (decode subunit).value = 0 then 1
      else min 2 (((decode total).value - (value reserved : ℚ≥0)) / (decode subunit).value) := by
  have zeroTest : (isZero subunit).1 = true ↔ (decode subunit).value = 0 := by
    simp [isZero_decode]
  by_cases empty : (decode subunit).value = 0
  · simp [budgetGain,zeroTest.mpr empty,empty]
  · have nonempty : ¬ (isZero subunit).1 = true := fun h => empty (zeroTest.mp h)
    rw [budgetGain,ite_eq_right nonempty,ite_eq_right empty]
    let ratio := (BinaryRational.div (subtractNat total reserved).1 subunit).1
    have ratio_value : (decode ratio).value =
        ((decode total).value - (value reserved : ℚ≥0)) / (decode subunit).value := by
      simp [ratio,subtractNat_value]
    have cmp : (BinaryRational.le ratio two).1 = true ↔ (decode ratio).value ≤ 2 := by
      rw [le_decode,RawNonnegativeRational.Code.le_eq_true,two_value]
    change (decode (if (BinaryRational.le ratio two).1 then ratio else two)).value = _
    rw [← ratio_value]
    by_cases small : (decode ratio).value ≤ 2
    · rw [ite_eq_left (cmp.mpr small),min_eq_right small]
    · rw [ite_eq_right (fun h => small (cmp.mp h)),min_eq_left (le_of_not_ge small),two_value]

private theorem ratio_stored (total : Fraction) (reserved : Bits) (subunit : Fraction) (K : ℕ)
    (fitTotal : StoredBounded total K) (fitSubunit : StoredBounded subunit K) :
    StoredBounded (BinaryRational.div (subtractNat total reserved).1 subunit).1 (2*K+2) := by
  have result := div_stored_bounded
    (BinaryFractionalRows.stored_raw_bound (subtractNat_stored total reserved fitTotal))
    (BinaryFractionalRows.stored_raw_bound fitSubunit)
  exact ⟨result.1.trans (by omega),result.2.trans (by omega)⟩

theorem budgetGain_stored (total : Fraction) (reserved : Bits) (subunit : Fraction) (K : ℕ)
    (fitTotal : StoredBounded total K) (fitSubunit : StoredBounded subunit K) :
    StoredBounded (budgetGain total reserved subunit).1 (2*K+2) := by
  unfold budgetGain
  dsimp only
  split
  · exact (smallConstants K).1
  · split
    · exact ratio_stored total reserved subunit K fitTotal fitSubunit
    · exact (smallConstants K).2

def budgetGainBound (K : ℕ) : ℕ :=
  4*(K+1)+(512*(K+1)^2+64*(4*K+2)+5)+2048*(K+1)^2+2048*(2*K+3)^2+8

theorem budgetGain_paid (total : Fraction) (reserved : Bits) (subunit : Fraction) (K : ℕ)
    (fitTotal : StoredBounded total K) (fitReserved : reserved.length ≤ K)
    (fitSubunit : StoredBounded subunit K) :
    (budgetGain total reserved subunit).2 ≤ budgetGainBound K := by
  have empty := isZero_charge fitSubunit
  have subtract := subtractNat_paid total reserved fitTotal fitReserved
  have divide := div_charge (subtractNat_stored total reserved fitTotal) fitSubunit
  have compare := le_charge (ratio_stored total reserved subunit K fitTotal fitSubunit) (smallConstants K).2
  rw [show 2*K+2+1 = 2*K+3 by omega] at compare
  unfold budgetGain budgetGainBound
  dsimp only
  split <;> dsimp only <;> omega

end DirectedFlowCutGap.BinaryRational
