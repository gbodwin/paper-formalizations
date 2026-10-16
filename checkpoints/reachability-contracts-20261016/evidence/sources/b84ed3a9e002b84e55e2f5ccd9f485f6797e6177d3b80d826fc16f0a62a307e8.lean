import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! The sourcewise reduction's optimization, including floor rounding and the
small-demand regime. Constants are deliberately uniform rather than optimized. -/
namespace SlackSparsification.Directed

theorem reachability_parameter (n p : ℕ) (hn : 0 < n) (hp : 0 < p) :
    ∃ l : ℕ, (p : ℝ) * l ≤ ((n : ℝ) * p) ^ (2 / 3 : ℝ) ∧
      Real.sqrt ((n : ℝ) * p * (2 * n / (l + 1) + 1 : ℕ)) ≤
        2 * ((n : ℝ) * p) ^ (2 / 3 : ℝ) := by
  let r := ((n : ℝ) * p) ^ (2 / 3 : ℝ)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hnp : (1 : ℝ) ≤ (n : ℝ) * p := by exact_mod_cast (show 1 ≤ n * p by nlinarith)
  have hr : 0 < r := Real.rpow_pos_of_pos (by positivity) _
  have hr3 : r ^ 3 = ((n : ℝ) * p) ^ 2 := by
    dsimp [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hnr : (n : ℝ) * p ≤ r ^ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le hnp (show (1 : ℝ) ≤ 4 / 3 by norm_num)
    change (n : ℝ) * p ≤ (((n : ℝ) * p) ^ (2 / 3 : ℝ)) ^ 2
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num at h ⊢
    exact h
  let l := ⌊r / p⌋₊
  have hl : (l : ℝ) ≤ r / p := Nat.floor_le (by positivity)
  have hl' : r / p < (l : ℝ) + 1 := Nat.lt_floor_add_one _
  have hpl : (p : ℝ) * l ≤ r := by
    have h := (le_div_iff₀ hp').mp hl
    nlinarith
  have hpl' : r < (p : ℝ) * ((l : ℝ) + 1) := by
    have h := (div_lt_iff₀ hp').mp hl'
    nlinarith
  let q := 2 * n / (l + 1)
  have hq : (q : ℝ) * ((l : ℝ) + 1) ≤ 2 * n := by exact_mod_cast Nat.div_mul_le_self (2*n) (l+1)
  have hbudget : (n : ℝ) * p * q ≤ 2 * r ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hq (show 0 ≤ (n : ℝ) * p by positivity)
    have h2 := mul_le_mul_of_nonneg_left hpl'.le (sq_nonneg r)
    have h3 : (n : ℝ)^2 * p ≤ r^2 * ((l : ℝ)+1) := by
      nlinarith [sq_nonneg ((n : ℝ)*p)]
    nlinarith
  refine ⟨l, hpl, ?_⟩
  apply (Real.sqrt_le_iff).mpr
  constructor
  · positivity
  · change (n : ℝ) * p * ((q + 1 : ℕ) : ℝ) ≤ _
    push_cast
    nlinarith

theorem reachability_slack_budget (n p : ℕ) (hn : 0 < n) (hp : 0 < p)
    (hlarge : n ≤ p ^ 2) (C : ℝ) (hC : 0 ≤ C) :
    ∃ l : ℕ, (p : ℝ) * l + 2 * C *
      (Real.sqrt ((n : ℝ) * p * (2 * n / (l + 1) + 1 : ℕ)) + n) ≤
      (1 + 6 * C) * (n : ℝ) ^ (2 / 3 : ℝ) * (p : ℝ) ^ (2 / 3 : ℝ) := by
  obtain ⟨l,hl,hs⟩ := reachability_parameter n p hn hp
  let r := ((n : ℝ)*p)^(2/3:ℝ)
  have hr : 0 ≤ r := by positivity
  have hr3 : r ^ 3 = ((n : ℝ) * p) ^ 2 := by
    dsimp [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnp : (n : ℝ) ≤ (p : ℝ)^2 := by exact_mod_cast hlarge
  have hnr : (n : ℝ) ≤ r := by
    by_contra hh
    have hh' : r < (n : ℝ) := by linarith
    have hc := pow_lt_pow_left₀ hh' hr (show 3 ≠ 0 by norm_num)
    nlinarith [mul_le_mul_of_nonneg_left hnp (sq_nonneg (n:ℝ))]
  refine ⟨l, ?_⟩
  rw [mul_assoc, ← Real.mul_rpow (by positivity) (by positivity)]
  change _ ≤ (1 + 6 * C) * r
  have h1 := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2*C by positivity)
  have h2 := mul_le_mul_of_nonneg_left hnr (show 0 ≤ 2*C by positivity)
  nlinarith
end SlackSparsification.Directed
