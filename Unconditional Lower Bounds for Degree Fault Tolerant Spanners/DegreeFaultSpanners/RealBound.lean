import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-! Exact bridge from the verified integer-power inequality to the paper's real exponents. -/

namespace DegreeFaultSpanners

/-- The explicit power inequality implies the paper's lower bound with constant 1/4. -/
theorem real_lower_bound_of_power (k f n m : ℕ) (hk : 1 ≤ k)
    (h : f ^ (k - 1) * n ^ (k + 1) ≤ 4 ^ k * m ^ k) :
    (1 / 4 : ℝ) * (f : ℝ) ^ (1 - 1 / (k : ℝ)) *
      (n : ℝ) ^ (1 + 1 / (k : ℝ)) ≤ (m : ℝ) := by
  have hk0 : k ≠ 0 := by omega
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk0
  have hef : (1 - 1 / (k : ℝ)) * (k : ℝ) = ((k - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hk, Nat.cast_one]
    field_simp <;> ring
  have hen : (1 + 1 / (k : ℝ)) * (k : ℝ) = ((k + 1 : ℕ) : ℝ) := by
    push_cast
    field_simp <;> ring
  have hp : ((f : ℝ) ^ (1 - 1 / (k : ℝ)) * (n : ℝ) ^ (1 + 1 / (k : ℝ))) ^ k ≤
      (4 * (m : ℝ)) ^ k := by
    rw [mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg f),
      ← Real.rpow_mul_natCast (Nat.cast_nonneg n), hef, hen,
      Real.rpow_natCast, Real.rpow_natCast, mul_pow]
    exact_mod_cast h
  have hroot := le_of_pow_le_pow_left₀ hk0 (by positivity : (0 : ℝ) ≤ 4 * (m : ℝ)) hp
  nlinarith

end DegreeFaultSpanners
