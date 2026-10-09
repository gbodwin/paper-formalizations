import DegreeFaultSpanners.RealBound

/-! A general explicit constant for the all-size lower-bound extension. -/

namespace DegreeFaultSpanners

/-- Convert any positive integer-factor power bound to the paper's real-exponent form. -/
theorem real_lower_bound_of_power_factor (k f n m A : ℕ)
    (hk : 1 ≤ k) (hA : 0 < A)
    (h : f ^ (k - 1) * n ^ (k + 1) ≤ A ^ k * m ^ k) :
    (1 / (A : ℝ)) * (f : ℝ) ^ (1 - 1 / (k : ℝ)) *
      (n : ℝ) ^ (1 + 1 / (k : ℝ)) ≤ (m : ℝ) := by
  have hk0 : k ≠ 0 := by omega
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk0
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  have hef : (1 - 1 / (k : ℝ)) * (k : ℝ) = ((k - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hk, Nat.cast_one]
    field_simp
  have hen : (1 + 1 / (k : ℝ)) * (k : ℝ) = ((k + 1 : ℕ) : ℝ) := by
    push_cast
    field_simp
  have hp : ((f : ℝ) ^ (1 - 1 / (k : ℝ)) * (n : ℝ) ^ (1 + 1 / (k : ℝ))) ^ k ≤
      ((A : ℝ) * (m : ℝ)) ^ k := by
    rw [mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg f),
      ← Real.rpow_mul_natCast (Nat.cast_nonneg n), hef, hen,
      Real.rpow_natCast, Real.rpow_natCast, mul_pow]
    exact_mod_cast h
  have hroot := le_of_pow_le_pow_left₀ hk0
    (by positivity : (0 : ℝ) ≤ (A : ℝ) * (m : ℝ)) hp
  calc
    (1 / (A : ℝ)) * (f : ℝ) ^ (1 - 1 / (k : ℝ)) *
        (n : ℝ) ^ (1 + 1 / (k : ℝ)) =
      ((f : ℝ) ^ (1 - 1 / (k : ℝ)) * (n : ℝ) ^ (1 + 1 / (k : ℝ))) / (A : ℝ) := by ring
    _ ≤ (m : ℝ) := (div_le_iff₀ hAR).mpr (by simpa only [mul_comm] using hroot)

end DegreeFaultSpanners
