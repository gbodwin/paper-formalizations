import MinorFreeSpanners.DensityAlgebra

namespace MinorFreeSpanners

/-- The density loss is linear and the constant2 independent of k.
The required dense-subgraph witness is still an explicit arithmetic premise. -/
theorem density_increment_linear_loss (k : ℕ) (d n m L h : ℝ)
    (hd : 0 ≤ d) (hn : 0 < n) (hm : 0 ≤ m) (hL : 0 ≤ L) (hh : 0 ≤ h)
    (hdense : n*d ≤ L*m) (hsize : n*d ≤ L*h^2)
    (hmoore : m^k ≤ 2^k*n^(k+1)) :
    d ≤ 2*L * h ^ (2/(k+1:ℝ)) := by
  have hp := density_increment_power k d n m L h hd hn hm hL hdense hsize hmoore
  have hcoef : (2*L)^k*L ≤ (2*L)^(k+1) := by
    rw [pow_succ]
    exact mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg (by positivity) k)
  have hp' := hp.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg h))
  have hr := Real.rpow_le_rpow (pow_nonneg hd (k+1)) hp'
    (inv_nonneg.mpr (show 0 ≤ ((k+1:ℕ):ℝ) by positivity))
  rw [Real.pow_rpow_inv_natCast hd (by omega),
    Real.mul_rpow (by positivity) (sq_nonneg h),
    Real.pow_rpow_inv_natCast (by positivity) (by omega),
    ← Real.rpow_natCast h 2, ← Real.rpow_mul hh] at hr
  simpa [div_eq_mul_inv] using hr

end MinorFreeSpanners
