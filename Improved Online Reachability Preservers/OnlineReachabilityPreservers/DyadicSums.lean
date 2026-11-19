import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Tactic

/-! Geometric estimates on finite sets of dyadic scales. -/

namespace OnlineReachabilityPreservers

open Finset

private theorem dyadic_rpow (r : ℝ) (j : ℕ) : ((2:ℝ)^j)^r = ((2:ℝ)^r)^j := by
  rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2), mul_comm,
    Real.rpow_mul (by norm_num), Real.rpow_natCast]

/-- A truncated geometric sum of positive powers of dyadic values. -/
theorem dyadic_sum_below (s : Finset ℕ) {r X : ℝ} (hr : 0 < r) (hX : 0 < X)
    (cut : ∀ j ∈ s, (2:ℝ)^j ≤ X) :
    (∑ j ∈ s, ((2:ℝ)^j)^r) ≤ ((2:ℝ)^r/((2:ℝ)^r-1))*X^r := by
  let q := (2:ℝ)^r
  have hq : 1 < q := by
    change 1 < (2:ℝ)^r
    conv_lhs => rw [← Real.rpow_zero (2:ℝ)]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hr
  have hd : 0 < q-1 := sub_pos.mpr hq
  have hp : 0 ≤ q := zero_le_one.trans hq.le
  change _ ≤ q/(q-1)*X^r
  rcases s.eq_empty_or_nonempty with he | hn
  · rw [he, sum_empty]
    exact mul_nonneg (div_nonneg hp hd.le) (Real.rpow_nonneg hX.le _)
  let m := s.max' hn
  have hm : m ∈ s := max'_mem _ _
  have hcap : q^m ≤ X^r := by
    change ((2:ℝ)^r)^m ≤ _
    rw [← dyadic_rpow]
    exact Real.rpow_le_rpow (by positivity) (cut m hm) hr.le
  calc
    _ = ∑ j ∈ s, q^j := by simp only [q, dyadic_rpow]
    _ ≤ ∑ j ∈ range (m+1), q^j := sum_le_sum_of_subset_of_nonneg
      (fun j hj => mem_range.mpr (Nat.lt_succ_of_le (le_max' _ _ hj)))
      (fun j _ _ => pow_nonneg hp j)
    _ = (q^(m+1)-1)/(q-1) := geom_sum_eq hq.ne' _
    _ ≤ q^(m+1)/(q-1) := div_le_div_of_nonneg_right (sub_le_self _ zero_le_one) hd.le
    _ = (q/(q-1))*q^m := by rw [pow_succ]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hcap (div_nonneg hp hd.le)

/-- A truncated geometric sum of negative powers of dyadic values. -/
theorem dyadic_sum_above (s : Finset ℕ) {r X : ℝ} (hr : r < 0) (hX : 0 < X)
    (cut : ∀ j ∈ s, X ≤ (2:ℝ)^j) :
    (∑ j ∈ s, ((2:ℝ)^j)^r) ≤ 1/(1-(2:ℝ)^r)*X^r := by
  let q := (2:ℝ)^r
  have hq : q < 1 := by
    change (2:ℝ)^r < 1
    conv_rhs => rw [← Real.rpow_zero (2:ℝ)]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hr
  have hp : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hd := sub_pos.mpr hq
  change _ ≤ 1/(1-q)*X^r
  rcases s.eq_empty_or_nonempty with he | hn
  · rw [he, sum_empty]
    exact mul_nonneg (one_div_pos.mpr hd).le (Real.rpow_nonneg hX.le _)
  let m := s.min' hn
  let M := s.max' hn
  have hm : m ∈ s := min'_mem _ _
  have hcap : q^m ≤ X^r := by
    change ((2:ℝ)^r)^m ≤ _
    rw [← dyadic_rpow]
    exact Real.rpow_le_rpow_of_nonpos hX (cut m hm) hr.le
  calc
    _ = ∑ j ∈ s, q^j := by simp only [q, dyadic_rpow]
    _ ≤ ∑ j ∈ Ico m (M+1), q^j := sum_le_sum_of_subset_of_nonneg (fun j hj =>
      mem_Ico.mpr ⟨min'_le _ _ hj, Nat.lt_succ_of_le (le_max' _ _ hj)⟩)
      (fun j _ _ => pow_nonneg hp j)
    _ ≤ q^m/(1-q) := geom_sum_Ico_le_of_lt_one hp hq
    _ ≤ X^r/(1-q) := div_le_div_of_nonneg_right hcap hd.le
    _ = _ := by ring

end OnlineReachabilityPreservers
