import DirectedFlowCutGap.BitSamplerCoupling

/-!
# Computable rejection confidence and counter widths

The trial budget is an integer binary width plus the requested failure
exponent. It discharges the accumulated finite-call error, including a zero
call budget. Counter bounds explicitly depend on the trial budget; arbitrary
confidence input is not priced using only the graph-size operand envelope.
The numerical exponent K represents log2(1/error). Polynomial dependence on K
is not a claim of polynomial dependence on its much shorter binary encoding.
-/
namespace DirectedFlowCutGap.FairBitConfidence
open FairBitWords

/-- `K` is the requested base-two error exponent. -/
def trials (Q K : ℕ) : ℕ := width Q + K

theorem scaled_failure_le_one (Q : ℕ) :
    (Q : ℝ) * ((1 : ℝ)/2)^(width Q) ≤ 1 := by
  have hq : (Q : ℝ) ≤ 2^(width Q) := by
    exact_mod_cast (Nat.le_of_lt (lt_bucket Q))
  have hp : (0 : ℝ) < 2^(width Q) := by positivity
  rw [div_pow, one_pow, mul_one_div]
  exact (div_le_one hp).mpr hq

/-- This actual choice bounds every accumulated call error by 2^(-K). -/
theorem accumulated_failure (Q K : ℕ) :
    (Q : ℝ) * ((1 : ℝ)/2)^(trials Q K) ≤ ((1 : ℝ)/2)^K := by
  calc
    (Q : ℝ) * ((1 : ℝ)/2)^(trials Q K) =
        ((Q : ℝ) * ((1 : ℝ)/2)^width Q) * ((1 : ℝ)/2)^K := by
      rw [trials, pow_add]
      ring
    _ ≤ 1 * ((1 : ℝ)/2)^K :=
      mul_le_mul_of_nonneg_right (scaled_failure_le_one Q) (by positivity)
    _ = _ := one_mul _

/-- The bit-count product and its increment fit a proved input-dependent width. -/
def counterWidth (Q T w : ℕ) : ℕ := width Q + width T + width w + 1

theorem counter_lt (Q T w : ℕ) : Q*T*w+1 < 2^(counterWidth Q T w) := by
  have hQ := lt_bucket Q
  have hT := lt_bucket T
  have hw := lt_bucket w
  have hpQ := bucket_pos Q
  have hpT := bucket_pos T
  have hpw := bucket_pos w
  have hQT : Q*T < bucket Q * bucket T :=
    (Nat.mul_le_mul_right T hQ.le).trans_lt ((Nat.mul_lt_mul_left hpQ).mpr hT)
  have hprod : Q*T*w < bucket Q * bucket T * bucket w :=
    (Nat.mul_le_mul_right w hQT.le).trans_lt
      ((Nat.mul_lt_mul_left (Nat.mul_pos hpQ hpT)).mpr hw)
  have hp : 0 < bucket Q * bucket T * bucket w := by positivity
  have he : 2^(counterWidth Q T w) = 2*(bucket Q * bucket T * bucket w) := by
    simp only [counterWidth, pow_add, pow_one, bucket]
    ring
  rw [he]
  omega

/-- The explicit trial counter has its own width even if Q is zero. -/
theorem trial_counter_le (T : ℕ) : T+1 ≤ 2^(width T) := by
  exact Nat.succ_le_of_lt (lt_bucket T)

/-- A coarse polynomial budget is available without treating a binary-encoded
confidence exponent as a constant. Sharper logarithmic bounds remain valid. -/
theorem trials_le (Q K : ℕ) : trials Q K ≤ Q+1+K := by
  have h := Nat.log_le_self 2 Q
  simp only [trials, width, Nat.log2_eq_log_two]
  omega

end DirectedFlowCutGap.FairBitConfidence
