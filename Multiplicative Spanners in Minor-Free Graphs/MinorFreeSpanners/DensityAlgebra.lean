import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! The quantitative algebra inside Lemma 16. This module does not assert
that a minor-free graph has the required density-increment witness.
Constructing that witness (Theorem 9) remains open. -/
namespace MinorFreeSpanners

/-- Eliminate the witness vertex count, keeping every constant explicit.
Here d is source density, n and m are the witness vertex/edge counts,
L is the density-increment loss, and h is the excluded clique size. -/
theorem density_increment_power (k : ℕ) (d n m L h : ℝ)
    (hd : 0 ≤ d) (hn : 0 < n) (hm : 0 ≤ m) (hL : 0 ≤ L)
    (hdense : n*d ≤ L*m) (hsize : n*d ≤ L*h^2)
    (hmoore : m^k ≤ 2^k*n^(k+1)) :
    d^(k+1) ≤ (2*L)^k*L*h^2 := by
  have hp : (n*d)^k ≤ (L*m)^k := pow_le_pow_left₀ (mul_nonneg hn.le hd) hdense k
  have hm' := mul_le_mul_of_nonneg_left hmoore (pow_nonneg hL k)
  have hc : n^k*d^k ≤ n^k*((2*L)^k*n) := by
    calc
      n^k*d^k = (n*d)^k := (mul_pow _ _ _).symm
      _ ≤ (L*m)^k := hp
      _ = L^k*m^k := mul_pow _ _ _
      _ ≤ L^k*(2^k*n^(k+1)) := hm'
      _ = n^k*((2*L)^k*n) := by rw [mul_pow,pow_succ]; ring
  have hd' : d^k ≤ (2*L)^k*n :=
    (mul_le_mul_iff_of_pos_left (pow_pos hn k)).mp hc
  calc
    d^(k+1) = d^k*d := pow_succ _ _
    _ ≤ ((2*L)^k*n)*d := mul_le_mul_of_nonneg_right hd' hd
    _ = (2*L)^k*(n*d) := by ring
    _ ≤ (2*L)^k*(L*h^2) :=
      mul_le_mul_of_nonneg_left hsize (pow_nonneg (by positivity) k)
    _ = (2*L)^k*L*h^2 := by ring

/-- The root extraction responsible for the exponent 2/(k+1). It is an
arithmetic consequence of the density-increment and Moore inequalities,
not a proof of the density-increment theorem itself. -/
theorem density_increment_exponent (k : ℕ) (d n m L h : ℝ)
    (hd : 0 ≤ d) (hn : 0 < n) (hm : 0 ≤ m) (hL : 0 ≤ L) (hh : 0 ≤ h)
    (hdense : n*d ≤ L*m) (hsize : n*d ≤ L*h^2)
    (hmoore : m^k ≤ 2^k*n^(k+1)) :
    d ≤ ((2*L)^k*L) ^ ((k+1:ℝ)⁻¹) * h ^ (2/(k+1:ℝ)) := by
  have hp := density_increment_power k d n m L h hd hn hm hL hdense hsize hmoore
  have hr := Real.rpow_le_rpow (pow_nonneg hd (k+1)) hp
    (inv_nonneg.mpr (show 0 ≤ (k+1:ℝ) by positivity))
  have hkn : k+1 ≠ 0 := by omega
  have hkcast : ((k+1:ℕ):ℝ) = (k+1:ℝ) := by push_cast; rfl
  rw [← hkcast, Real.pow_rpow_inv_natCast hd hkn,
    Real.mul_rpow (by positivity) (sq_nonneg h), hkcast] at hr
  rw [← Real.rpow_natCast h 2, ← Real.rpow_mul hh] at hr
  simpa [div_eq_mul_inv] using hr

end MinorFreeSpanners
