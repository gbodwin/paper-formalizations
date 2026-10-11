import SlackSparsification.PlusFourParameters
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

namespace SlackSparsification

/-- Optimize the +6 construction relative to the cited subset-spanner
constant C. Integer thresholds include m=0. -/
theorem plus_six_integer_budget (n p k : ℕ) (hk : 0 < k) (hp : p ≤ k ^ 4)
    (C : ℝ) (hC : 0 ≤ C) :
    ((3 * n * k + 2 * p * (n / k ^ 3) : ℕ) : ℝ) +
      C * n * Real.sqrt (2 * (2 * n / (k * (n / k ^ 3 + 1)) + 1) : ℕ) ≤
        (5 + 3 * C) * n * k := by
  let m := n / k ^ 3
  have hm : m * k ^ 3 ≤ n := Nat.div_mul_le_self _ _
  have hm' : n < k * (m + 1) * k ^ 2 := by
    have h := Nat.lt_mul_div_succ n (show 0 < k ^ 3 by positivity)
    change n < k ^ 3 * (m + 1) at h
    convert h using 1 <;> ring
  have hshort : p * m ≤ n * k := calc
    _ ≤ k ^ 4 * m := Nat.mul_le_mul_right m hp
    _ = k * (m * k ^ 3) := by ring
    _ ≤ k * n := Nat.mul_le_mul_left _ hm
    _ = _ := by ac_rfl
  have hroot := root_quotient_bound n k m (k ^ 2) hk hm'
  have hk2 : 1 ≤ k ^ 2 := one_le_pow₀ (by omega)
  have hs : 2 * (2 * n / (k * (m + 1)) + 1) ≤ 6 * k ^ 2 := by omega
  have hs' : ((2 * (2 * n / (k * (m + 1)) + 1) : ℕ) : ℝ) ≤ 6 * (k : ℝ) ^ 2 := by exact_mod_cast hs
  have hsqrt : Real.sqrt (2 * (2 * n / (k * (m + 1)) + 1) : ℕ) ≤ 3 * (k : ℝ) := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by positivity, by nlinarith⟩
  have hcost := mul_le_mul_of_nonneg_left hsqrt (show (0 : ℝ) ≤ C * n by positivity)
  have hshort' : (p : ℝ) * m ≤ (n : ℝ) * k := by exact_mod_cast hshort
  change ((3 * n * k + 2 * p * m : ℕ) : ℝ) + _ ≤ _
  push_cast
  nlinarith

/-- A rounded fourth root has both the combinatorial and analytic bounds
needed by the construction. -/
theorem exists_fourth_parameter (p : ℕ) (hp : 0 < p) :
    ∃ k : ℕ, 0 < k ∧ p ≤ k ^ 4 ∧ (k : ℝ) ≤ 2 * (p : ℝ) ^ (1 / 4 : ℝ) := by
  let r : ℝ := (p : ℝ) ^ (1 / 4 : ℝ)
  have hr : 1 ≤ r := Real.one_le_rpow (by exact_mod_cast (show 1 ≤ p by omega)) (by norm_num)
  have hr0 : 0 ≤ r := by linarith
  let k := ⌈r⌉₊
  have hkr : r ≤ (k : ℝ) := Nat.le_ceil r
  have hkle : (k : ℝ) < r + 1 := Nat.ceil_lt_add_one hr0
  have hk : 0 < k := by
    have : (0 : ℝ) < k := by linarith
    exact_mod_cast this
  have hcube : r ^ 4 = (p : ℝ) := by
    dsimp [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hpc : p ≤ k ^ 4 := by
    have h := pow_le_pow_left₀ hr0 hkr 4
    rw [hcube] at h
    exact_mod_cast h
  exact ⟨k, hk, hpc, by linarith⟩

end SlackSparsification
