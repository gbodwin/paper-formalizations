import MinorFreeSpanners.CanonicalCorrectedGirth
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-! Select a literal integer multiplier from the stretch slack. The same
choice meets the corrected weighted-girth threshold and retains an explicit
inverse-slack bound; it is not an extra asymptotic parameter assumption. -/
namespace MinorFreeSpanners

noncomputable def canonicalScale (eps : ℝ) : ℕ := 4096 + ⌈4000/eps⌉₊

 theorem canonicalScale_bounds (eps : ℝ) (heps : 0<eps) (heps1 : eps≤1) :
    4096≤canonicalScale eps ∧ 4000≤(canonicalScale eps:ℝ)*eps ∧
      (canonicalScale eps:ℝ)≤8097/eps := by
  have hq : 0≤4000/eps := by positivity
  have hlo := Nat.le_ceil (4000/eps)
  have hhi := Nat.ceil_lt_add_one hq
  have hmul := mul_le_mul_of_nonneg_right hlo heps.le
  have hid : (4000/eps)*eps=4000 := div_mul_cancel₀ _ heps.ne'
  constructor
  · dsimp [canonicalScale]
    omega
  constructor
  · dsimp [canonicalScale]
    push_cast
    rw [hid] at hmul
    nlinarith only [hmul,heps]
  · apply (le_div_iff₀ heps).mpr
    dsimp [canonicalScale]
    push_cast
    have hmulhi := mul_lt_mul_of_pos_right hhi heps
    rw [add_mul,hid] at hmulhi
    nlinarith only [hmulhi,heps1]

 theorem canonicalScale_corrected_girth (eps : ℝ) (heps : 0<eps) (heps1 : eps≤1)
    (r : ℕ) (hr : 1≤r) :
    2*(r:ℝ)*(1+2000/(canonicalScale eps:ℝ))≤(1+eps)*(2*(r:ℝ)-1)+1 := by
  obtain ⟨ht,hscale,_⟩ := canonicalScale_bounds eps heps heps1
  exact canonical_girth_below_corrected_threshold (canonicalScale eps) r eps (by omega) hr hscale

end MinorFreeSpanners
