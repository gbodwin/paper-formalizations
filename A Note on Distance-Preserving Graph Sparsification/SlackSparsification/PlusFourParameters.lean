import SlackSparsification.ParameterBounds
import Mathlib.Tactic

namespace SlackSparsification

/-- A reusable division estimate for deterministic hitting-set costs. -/
theorem root_quotient_bound (n d l k : ℕ) (hd : 0 < d)
    (h : n < d * (l + 1) * k) : 2 * n / (d * (l + 1)) ≤ 2 * k := by
  have hden : 0 < d * (l + 1) := by positivity
  have hb : 2 * n < (2 * k + 1) * (d * (l + 1)) := by nlinarith
  have hq := (Nat.div_lt_iff_lt_mul hden).mpr hb
  omega

/-- Integer optimization for Theorem 12. At p≤k⁷, use d=k²,
m=floor(n/k⁵), K=floor(n/k⁴). The bound includes all zero-threshold cases. -/
theorem plus_four_integer_budget (n p k : ℕ) (hk : 0 < k) (hp : p ≤ k ^ 7) :
    3 * n * (k ^ 2) + 2 * p * (n / k ^ 5) +
      (2 * (2 * n / (k ^ 2 * (n / k ^ 5 + 1)) + 1)) ^ 2 * (n / k ^ 4) +
      n * (2 * n / (k ^ 2 * (n / k ^ 4 + 1)) + 1) ≤ 44 * n * k ^ 2 := by
  let m := n / k ^ 5
  let K := n / k ^ 4
  have hm : m * k ^ 5 ≤ n := Nat.div_mul_le_self _ _
  have hK : K * k ^ 4 ≤ n := Nat.div_mul_le_self _ _
  have hm' : n < k ^ 2 * (m + 1) * k ^ 3 := by
    have h := Nat.lt_mul_div_succ n (show 0 < k ^ 5 by positivity)
    change n < k ^ 5 * (m + 1) at h
    convert h using 1 <;> ring
  have hK' : n < k ^ 2 * (K + 1) * k ^ 2 := by
    have h := Nat.lt_mul_div_succ n (show 0 < k ^ 4 by positivity)
    change n < k ^ 4 * (K + 1) at h
    convert h using 1 <;> ring
  have hshort : p * m ≤ n * k ^ 2 := calc
    _ ≤ k ^ 7 * m := Nat.mul_le_mul_right m hp
    _ = k ^ 2 * (m * k ^ 5) := by ring
    _ ≤ k ^ 2 * n := Nat.mul_le_mul_left _ hm
    _ = _ := by ac_rfl
  have hroot := root_quotient_bound n (k ^ 2) m (k ^ 3) (by positivity) hm'
  have hk3 : 1 ≤ k ^ 3 := by exact one_le_pow₀ (by omega)
  have hs : 2 * (2 * n / (k ^ 2 * (m + 1)) + 1) ≤ 6 * k ^ 3 := by omega
  have hmid : (2 * (2 * n / (k ^ 2 * (m + 1)) + 1)) ^ 2 * K ≤ 36 * n * k ^ 2 := calc
    _ ≤ (6 * k ^ 3) ^ 2 * K := Nat.mul_le_mul_right K (Nat.pow_le_pow_left hs 2)
    _ = (36 * k ^ 2) * (K * k ^ 4) := by ring
    _ ≤ (36 * k ^ 2) * n := Nat.mul_le_mul_left _ hK
    _ = _ := by ring
  have hlongRoot := root_quotient_bound n (k ^ 2) K (k ^ 2) (by positivity) hK'
  have hk2 : 1 ≤ k ^ 2 := by exact one_le_pow₀ (by omega)
  have hlong : n * (2 * n / (k ^ 2 * (K + 1)) + 1) ≤ 3 * n * k ^ 2 := by
    have hr : 2 * n / (k ^ 2 * (K + 1)) + 1 ≤ 3 * k ^ 2 := by omega
    have h := Nat.mul_le_mul_left n hr
    nlinarith
  change 3 * n * k ^ 2 + 2 * p * m +
    (2 * (2 * n / (k ^ 2 * (m + 1)) + 1)) ^ 2 * K +
    n * (2 * n / (k ^ 2 * (K + 1)) + 1) ≤ _
  nlinarith

/-- A rounded seventh root with the exact exponent conversion used in +4. -/
theorem exists_seventh_parameter (p : ℕ) (hp : 0 < p) :
    ∃ k : ℕ, 0 < k ∧ p ≤ k ^ 7 ∧ ((k ^ 2 : ℕ) : ℝ) ≤ 4 * (p : ℝ) ^ (2 / 7 : ℝ) := by
  let r : ℝ := (p : ℝ) ^ (1 / 7 : ℝ)
  have hr : 1 ≤ r := Real.one_le_rpow (by exact_mod_cast (show 1 ≤ p by omega)) (by norm_num)
  have hr0 : 0 ≤ r := by linarith
  let k := ⌈r⌉₊
  have hkr : r ≤ (k : ℝ) := Nat.le_ceil r
  have hkle : (k : ℝ) < r + 1 := Nat.ceil_lt_add_one hr0
  have hk : 0 < k := by
    have h : (0 : ℝ) < k := by linarith
    exact_mod_cast h
  have hpower : r ^ 7 = (p : ℝ) := by
    dsimp [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hpc : p ≤ k ^ 7 := by
    have h := pow_le_pow_left₀ hr0 hkr 7
    rw [hpower] at h
    exact_mod_cast h
  have hr2 : r ^ 2 = (p : ℝ) ^ (2 / 7 : ℝ) := by
    dsimp [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hk2 := pow_le_pow_left₀ (show (0 : ℝ) ≤ k by positivity) (show (k : ℝ) ≤ 2 * r by linarith) 2
  refine ⟨k, hk, hpc, ?_⟩
  push_cast
  nlinarith

end SlackSparsification
