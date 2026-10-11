import MinorFreeSpanners.BipartiteRightMinor

/-! A numerical density gain for the actual right quotient, on the explicit
inverse-quadratic bipartite cleaning domain and a supplied retained-center
count. Construction of that count is a subsequent graph join. -/
namespace MinorFreeSpanners

/-- Explicit arithmetic paying regularization, removed centers and cleaning
from their separate proved budgets. The retained center count is explicit. -/
theorem bipartite_right_density_gain (k ell d m B C E : ℝ)
    (hk : 0 < k) (hell : 0 ≤ ell) (hellk : 4*ell ≤ k)
    (hd : 0 ≤ d) (hB : 0 ≤ B) (hC : 0 ≤ C) (hCB : C ≤ B)
    (hcenters : 5*k^2*C+ell*B ≥ 5*k^2*B)
    (hm : (1-1/(100*k))*d ≤ m)
    (hedges : m*ell*C ≤ E+(2*ell*d/k)*C) :
    (ell-1)*d*B ≤ E := by
  have hk2 : 0 < 5*k^2 := by positivity
  have hratio : ell/k ≤ 1/4 := (div_le_iff₀ hk).mpr (by linarith)
  have hratio0 : 0 ≤ ell/k := by positivity
  have hsquare : 16*ell^2 ≤ k^2 := by
    nlinarith [mul_nonneg (show 0 ≤ k-4*ell by linarith)
      (show 0 ≤ k+4*ell by positivity)]
  have hcoef : ell^2/(5*k^2) ≤ 1/80 := (div_le_iff₀ hk2).mpr (by nlinarith)
  have hmissing : B-C ≤ ell*B/(5*k^2) := (le_div_iff₀ hk2).mpr (by nlinarith)
  have hmissing' : ell*(B-C) ≤ B/80 := calc
    _ ≤ ell*(ell*B/(5*k^2)) := mul_le_mul_of_nonneg_left hmissing hell
    _ = (ell^2/(5*k^2))*B := by ring
    _ ≤ (1/80)*B := mul_le_mul_of_nonneg_right hcoef hB
    _ = _ := by ring
  have hselected : ell*d*(B-C) ≤ d*B/80 := by
    have hh := mul_le_mul_of_nonneg_left hmissing' hd
    nlinarith
  have hDC : d*C ≤ d*B := mul_le_mul_of_nonneg_left hCB hd
  have hDC0 : 0 ≤ d*C := mul_nonneg hd hC
  have hregular : ell*(1-1/(100*k))*d*C ≤ m*ell*C := by
    have hh := mul_le_mul_of_nonneg_right hm (mul_nonneg hell hC)
    nlinarith
  have hregularloss : ell*(1/(100*k))*d*C ≤ d*B/400 := calc
    _ = (ell/k)*(d*C)/100 := by ring
    _ ≤ (1/4)*(d*C)/100 := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hratio hDC0) (by norm_num)
    _ ≤ (1/4)*(d*B)/100 := by linarith
    _ = _ := by ring
  have hclean : (2*ell*d/k)*C ≤ d*B/2 := calc
    _ = 2*(ell/k)*(d*C) := by ring
    _ ≤ 2*(1/4)*(d*C) := by nlinarith [mul_le_mul_of_nonneg_right hratio hDC0]
    _ ≤ d*B/2 := by linarith
  have hmass : 0 ≤ d*B := mul_nonneg hd hB
  nlinarith

end MinorFreeSpanners
