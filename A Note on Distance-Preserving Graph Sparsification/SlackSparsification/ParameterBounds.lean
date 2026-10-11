import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Integer parameter choices for Theorem 8. The use of floor(n/k²)
handles thresholds below one without adding an uncontrolled O(p) term. -/
namespace SlackSparsification

/-- The three costs of the +2 slack construction are bounded by 7nk when
p ≤ k³. This includes n = 0 and m = floor(n/k²) = 0. -/
theorem plus_two_integer_budget (n p k : ℕ) (hk : 0 < k) (hp : p ≤ k ^ 3) :
    3 * n * k + p * (n / k ^ 2) +
      n * (2 * n / (k * (n / k ^ 2 + 1)) + 1) ≤ 7 * n * k := by
  let m := n / k ^ 2
  have hm : m * k ^ 2 ≤ n := Nat.div_mul_le_self _ _
  have hm' : n < (m + 1) * k ^ 2 := by
    simpa [m, Nat.mul_comm] using Nat.lt_mul_div_succ n (show 0 < k ^ 2 by positivity)
  have hshort : p * m ≤ n * k := by
    have ha := Nat.mul_le_mul_right m hp
    have hb := Nat.mul_le_mul_right k hm
    nlinarith
  have hden : 0 < k * (m + 1) := by positivity
  have hlong : 2 * n / (k * (m + 1)) ≤ 2 * k := by
    have h : 2 * n < (2 * k + 1) * (k * (m + 1)) := by
      have ha := Nat.mul_lt_mul_of_pos_left hm' (show 0 < 2 by omega)
      have hb : 0 < k * (m + 1) := hden
      nlinarith
    have hd := (Nat.div_lt_iff_lt_mul hden).mpr h
    omega
  change 3 * n * k + p * m + n * (2 * n / (k * (m + 1)) + 1) ≤ _
  have hroot := Nat.mul_le_mul_left n hlong
  have hn := Nat.mul_le_mul_left n (show 1 ≤ k by omega)
  nlinarith

/-- A rounded cube root has both the combinatorial and analytic bounds
needed by the construction. -/
theorem exists_cube_parameter (p : ℕ) (hp : 0 < p) :
    ∃ k : ℕ, 0 < k ∧ p ≤ k ^ 3 ∧ (k : ℝ) ≤ 2 * (p : ℝ) ^ (1 / 3 : ℝ) := by
  let r : ℝ := (p : ℝ) ^ (1 / 3 : ℝ)
  have hr : 1 ≤ r := Real.one_le_rpow (by exact_mod_cast (show 1 ≤ p by omega)) (by norm_num)
  have hr0 : 0 ≤ r := by linarith
  let k := ⌈r⌉₊
  have hkr : r ≤ (k : ℝ) := Nat.le_ceil r
  have hkle : (k : ℝ) < r + 1 := Nat.ceil_lt_add_one hr0
  have hk : 0 < k := by
    have : (0 : ℝ) < k := by linarith
    exact_mod_cast this
  have hcube : r ^ 3 = (p : ℝ) := by
    dsimp [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hpc : p ≤ k ^ 3 := by
    have h := pow_le_pow_left₀ hr0 hkr 3
    rw [hcube] at h
    exact_mod_cast h
  exact ⟨k, hk, hpc, by linarith⟩

end SlackSparsification
