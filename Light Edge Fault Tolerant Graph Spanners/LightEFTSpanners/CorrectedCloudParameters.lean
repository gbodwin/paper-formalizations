import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-! Literal rounding and constants for the corrected cf-cloud lower bound. -/
namespace LightEFTSpanners.CorrectedCloud

noncomputable def cloudSize (c : ℝ) (f : ℕ) : ℕ := ⌊c*(f:ℝ)⌋₊

theorem two_mul_le_cloudSize {c : ℝ} (hc : 2≤c) (f : ℕ) :
    2*f≤cloudSize c f := by
  apply Nat.le_floor
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg f : (0:ℝ)≤f)]

theorem fault_lt_cloudSize {c : ℝ} (hc : 2≤c) {f : ℕ} (hf : 1≤f) :
    f<cloudSize c f := by
  have h := two_mul_le_cloudSize hc f
  omega

theorem two_le_cloudSize {c : ℝ} (hc : 2≤c) {f : ℕ} (hf : 1≤f) :
    2≤cloudSize c f := by
  have h := two_mul_le_cloudSize hc f
  omega

theorem cloudSize_cast_le {c : ℝ} (hc : 2≤c) (f : ℕ) :
    (cloudSize c f : ℝ)≤c*(f:ℝ) := by
  apply Nat.floor_le
  positivity

theorem cloudSize_coefficient {c : ℝ} (hc : 2≤c) (f : ℕ) :
    1/(2*c)≤((f:ℝ)+1)/(2*(cloudSize c f : ℝ)+1) := by
  have hp := cloudSize_cast_le hc f
  apply (div_le_div_iff₀ (by positivity : (0:ℝ)<2*c)
    (by positivity : (0:ℝ)<2*(cloudSize c f : ℝ)+1)).mpr
  nlinarith

theorem core_order_ge_scaled_order {c : ℝ} (hc : 2≤c) {f : ℕ} (hf : 1≤f)
    (m : ℕ) : ⌊((m*cloudSize c f : ℕ):ℝ)/(c*(f:ℝ))⌋₊≤m := by
  have hcf : 0<c*(f:ℝ) := by positivity
  apply Nat.floor_le_of_le
  apply (div_le_iff₀ hcf).mpr
  simpa only [Nat.cast_mul] using
    mul_le_mul_of_nonneg_left (cloudSize_cast_le hc f) (Nat.cast_nonneg m : (0:ℝ)≤m)

end LightEFTSpanners.CorrectedCloud
