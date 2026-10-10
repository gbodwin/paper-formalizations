import VFTSpanners.EdgeMain
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace VFTSpanners
open SimpleGraph
attribute [local instance] Classical.propDecidable

/-- Translate the checked integer-power estimate into the paper's real exponents. -/
theorem real_bound_of_power_bound (m n f r : ℕ) (hr : 1 ≤ r)
    (h : m^r ≤ 72^r*n^(r+1)*f^(r-1)) :
    (m : ℝ) ≤ 72*(n : ℝ)^(1+1/(r : ℝ))*(f : ℝ)^(1-1/(r : ℝ)) := by
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
  have hreal : (m : ℝ)^r ≤ (72 : ℝ)^r*(n : ℝ)^(r+1)*(f : ℝ)^(r-1) := by
    exact_mod_cast h
  have hroot := Real.rpow_le_rpow (by positivity) hreal (by positivity : 0 ≤ (r : ℝ)⁻¹)
  rw [Real.pow_rpow_inv_natCast (by positivity) (by omega)] at hroot
  rw [Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) (by positivity),
    Real.pow_rpow_inv_natCast (by positivity) (by omega)] at hroot
  have hnexp : ((r+1 : ℕ) : ℝ)*(r : ℝ)⁻¹ = 1+1/(r : ℝ) := by
    push_cast
    field_simp
  have hfexp : ((r-1 : ℕ) : ℝ)*(r : ℝ)⁻¹ = 1-1/(r : ℝ) := by
    rw [Nat.cast_sub hr]
    push_cast
    field_simp
  rw [← Real.rpow_natCast_mul (Nat.cast_nonneg n),
    ← Real.rpow_natCast_mul (Nat.cast_nonneg f), hnexp, hfexp] at hroot
  exact hroot

theorem vft_corollary_two_real {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : Sym2 V → ℝ) (r f : ℕ)
    (hr : 1 ≤ r) (hf : 1 ≤ f) (hw : ∀ e, 0 ≤ w e) :
    ((greedyOutput G w (2*r-1) f).edgeFinset.card : ℝ) ≤
      72*(Fintype.card V : ℝ)^(1+1/(r : ℝ))*(f : ℝ)^(1-1/(r : ℝ)) :=
  real_bound_of_power_bound _ _ _ _ hr (corollary_two_size G w r f hr hf hw)

theorem eft_corollary_two_real {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : Sym2 V → ℝ) (r f : ℕ)
    (hr : 1 ≤ r) (hf : 1 ≤ f) (hw : ∀ e, 0 ≤ w e) :
    ((edgeGreedyOutput G w (2*r-1) f).edgeFinset.card : ℝ) ≤
      72*(Fintype.card V : ℝ)^(1+1/(r : ℝ))*(f : ℝ)^(1-1/(r : ℝ)) :=
  real_bound_of_power_bound _ _ _ _ hr (eft_corollary_two_size G w r f hr hf hw)

end VFTSpanners
