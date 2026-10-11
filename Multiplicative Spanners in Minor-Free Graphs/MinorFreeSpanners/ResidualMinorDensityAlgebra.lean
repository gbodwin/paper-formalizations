import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-! Numerical join for the actual singleton-deletion minor. The inputs are
its real edge budget and exact family/remaining-singleton counts. -/
namespace MinorFreeSpanners

/-- Large leftover singletons are paid by the original degree sum. The
constant-seven density loss includes the complete 4 eps2 clean allowance. -/
theorem retained_minor_density_algebra (k d a c b r e : ℝ)
    (hk : 8 ≤ k) (hd : 0 ≤ d) (hc : 0 ≤ c) (hb : 0 ≤ b)
    (hr : r ≤ b) (hlarge : k^2*b ≤ k*c+r) (ha : a*k ≤ 5)
    (hedge : d*(k*c+r-b-c-a*k*c) ≤ e) :
    (k-7)*d*(c+r) ≤ e := by
  have hpos : 0 < k := by linarith
  have hbscale : 0 ≤ (7*k-1)*b := mul_nonneg (by linarith) hb
  have hmul : k*((k-7)*b) ≤ k*c := by nlinarith only [hlarge,hr,hbscale]
  have hbc : (k-7)*b ≤ c := le_of_mul_le_mul_left hmul hpos
  have hrscale := mul_le_mul_of_nonneg_left hr (show 0 ≤ k-8 by linarith)
  have hbase : (k-7)*(c+r) ≤ k*c+r-b-6*c := by nlinarith only [hbc,hrscale]
  have haloss := mul_le_mul_of_nonneg_right ha hc
  have hloss : (k-7)*(c+r) ≤ k*c+r-b-c-a*k*c := by nlinarith only [hbase,haloss]
  have h := mul_le_mul_of_nonneg_left hloss hd
  convert h.trans hedge using 1; ring

/-- The inverse-square/inverse-linear parameter choice discharges the
actual combined residual and contraction loss coefficient. -/
theorem residual_loss_coefficient (k eps1 eps2 : ℝ) (hk : 3 ≤ k)
    (he1 : eps1*k^2 ≤ 1) (he2 : eps2*k ≤ 1) :
    (3*eps1+4*eps2)*k ≤ 5 := by
  have hp : 0 < k := by linarith
  have h1 : 3*eps1*k ≤ 1 := by
    have hh : k*(3*eps1*k) ≤ k := by nlinarith only [he1,hk]
    exact le_of_mul_le_mul_left (by simpa using hh) hp
  nlinarith only [h1,he2]

end MinorFreeSpanners
