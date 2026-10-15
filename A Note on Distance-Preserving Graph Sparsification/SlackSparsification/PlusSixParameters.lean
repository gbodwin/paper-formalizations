import SlackSparsification.PlusFourParameters
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! Integer rounding for conditional +6: d=k and m=floor(n/k^3).
There is no lower bound on n or on m. -/
namespace SlackSparsification

/-- The constructed root-set cap is at most 6k², including m=0. -/
theorem plus_six_root_bound (n k : ℕ) (hk : 0 < k) :
    2 * (2 * n / (k * (n / k ^ 3 + 1)) + 1) ≤ 6 * k ^ 2 := by
  have hn : n < k * (n / k ^ 3 + 1) * k ^ 2 := by
    have h := Nat.lt_mul_div_succ n (show 0 < k ^ 3 by positivity)
    convert h using 1; ring
  have hq := root_quotient_bound n k (n / k ^ 3) (k ^ 2) hk hn
  have hk2 : 1 ≤ k ^ 2 := one_le_pow₀ (by omega)
  omega

/-- Explicit cost (5+3C)nk when p≤k⁴. The square-root term is real;
all divisions in the root cardinality and path purchases are natural. -/
theorem plus_six_integer_budget (n p k : ℕ) (hk : 0 < k) (hp : p ≤ k ^ 4)
    (C : ℝ) (hC : 0 < C) :
    (3 * n * k + 2 * p * (n / k ^ 3) : ℕ) +
      C * n * Real.sqrt (2 * (2 * n / (k * (n / k ^ 3 + 1)) + 1) : ℕ) ≤
        (5 + 3 * C) * n * k := by
  have hm : (n / k ^ 3) * k ^ 3 ≤ n := Nat.div_mul_le_self _ _
  have hshort : p * (n / k ^ 3) ≤ n * k := calc
    _ ≤ k ^ 4 * (n / k ^ 3) := Nat.mul_le_mul_right _ hp
    _ = ((n / k ^ 3) * k ^ 3) * k := by ring
    _ ≤ _ := Nat.mul_le_mul_right k hm
  have hbase : 3 * n * k + 2 * p * (n / k ^ 3) ≤ 5 * n * k := by nlinarith only [hshort]
  have hb : ((3 * n * k + 2 * p * (n / k ^ 3) : ℕ) : ℝ) ≤ 5 * (n : ℝ) * k := by
    exact_mod_cast hbase
  have hr : ((2 * (2 * n / (k * (n / k ^ 3 + 1)) + 1) : ℕ) : ℝ) ≤ 6 * (k : ℝ) ^ 2 := by
    exact_mod_cast plus_six_root_bound n k hk
  have hs : Real.sqrt (2 * (2 * n / (k * (n / k ^ 3 + 1)) + 1) : ℕ) ≤ 3 * (k : ℝ) := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith [sq_nonneg (k : ℝ)]
  have hc := mul_le_mul_of_nonneg_left hs (show 0 ≤ C * n by positivity)
  nlinarith

/-- A rounded fourth root with explicit uniform factor two. -/
theorem exists_fourth_parameter (p : ℕ) (hp : 0 < p) :
    ∃ k : ℕ, 0 < k ∧ p ≤ k ^ 4 ∧ (k : ℝ) ≤ 2 * (p : ℝ) ^ (1 / 4 : ℝ) := by
  let r : ℝ := (p : ℝ) ^ (1 / 4 : ℝ)
  have hr : 1 ≤ r := Real.one_le_rpow (by exact_mod_cast (show 1 ≤ p by omega)) (by norm_num)
  have hr0 : 0 ≤ r := by linarith
  let k := ⌈r⌉₊
  have hkr : r ≤ (k : ℝ) := Nat.le_ceil r
  have hkle : (k : ℝ) < r + 1 := Nat.ceil_lt_add_one hr0
  have hk : 0 < k := by
    have h : (0 : ℝ) < k := by linarith
    exact_mod_cast h
  have hpower : r ^ 4 = (p : ℝ) := by
    dsimp [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hpc : p ≤ k ^ 4 := by
    have h := pow_le_pow_left₀ hr0 hkr 4
    rw [hpower] at h
    exact_mod_cast h
  exact ⟨k, hk, hpc, by linarith⟩

end SlackSparsification
