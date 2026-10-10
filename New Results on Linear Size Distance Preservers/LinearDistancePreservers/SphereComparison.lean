import LinearDistancePreservers.TheoremFourRateAudit

/-! Algebra for the elementary-sphere alternative. This file does not yet
claim a parameter-selected graph theorem. -/
namespace LinearDistancePreservers.SphereRate

noncomputable def logRatio (d L t : ℝ) : ℝ :=
  ((3*d-2)*t-(2/3)*L)/(d^2-2)

theorem sharp_difference {d L t : ℝ} (hd : 2 ≤ d) :
    TheoremFourRateAudit.logRatio d L ((2/3)*L-t) - logRatio d L t =
      2*((d+2)*L-(6*d+3)*t)/(3*d*(d+1)*(d^2-2)) := by
  rw [TheoremFourRateAudit.deficit_identity (by linarith)]
  have hd0 : d ≠ 0 := by linarith
  have hd1 : d+1 ≠ 0 := by linarith
  have hd2 : d^2-2 ≠ 0 := by nlinarith
  unfold logRatio
  field_simp
  ring

/-- The sharp polynomial rate and elementary-sphere rate differ by at
most O(L/d³), independently of any geometric dimension coefficient. -/
theorem sharp_le_sphere_add {d L t : ℝ} (hd : 2 ≤ d)
    (hL : 0 ≤ L) (ht : 0 ≤ t) :
    TheoremFourRateAudit.logRatio d L ((2/3)*L-t) ≤
      logRatio d L t + 4*L/d^3 := by
  have hd0 : 0 < d := by linarith
  have hd2 : 0 < d^2-2 := by nlinarith
  have hden : d^4 ≤ 3*d*(d+1)*(d^2-2) := by
    have hquad : d^2/2 ≤ d^2-2 := by nlinarith
    have hprod : d*(d^2/2) ≤ (d+1)*(d^2-2) :=
      mul_le_mul (by linarith) hquad (by positivity) (by positivity)
    have hh := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 3*d by positivity)
    nlinarith [sq_nonneg (d^2)]
  have hnum : 2*((d+2)*L-(6*d+3)*t) ≤ 4*d*L := by
    have ht' : 0 ≤ (6*d+3)*t := by positivity
    have hL' := mul_nonneg (show 0 ≤ d-2 by linarith) hL
    nlinarith
  have hdiff :
      TheoremFourRateAudit.logRatio d L ((2/3)*L-t) - logRatio d L t ≤ 4*L/d^3 := by
    rw [sharp_difference hd]
    calc
      _ ≤ (4*d*L)/(3*d*(d+1)*(d^2-2)) :=
        div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ (4*d*L)/d^4 := div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = 4*L/d^3 := by field_simp
  linarith

/-- In the moderate-dimension regime the replacement costs only another
constant multiple of sqrt(log N) in the logarithmic lower bound. -/
theorem sharp_le_sphere_sqrt {d L t : ℝ} (hd : 2 ≤ d)
    (hL : 0 ≤ L) (ht : 0 ≤ t) (hbudget : Real.sqrt L ≤ d^3) :
    TheoremFourRateAudit.logRatio d L ((2/3)*L-t) ≤
      logRatio d L t + 4*Real.sqrt L := by
  apply (sharp_le_sphere_add hd hL ht).trans
  gcongr
  apply (div_le_iff₀ (by positivity : 0 < d^3)).mpr
  have hh := mul_le_mul_of_nonneg_left hbudget (Real.sqrt_nonneg L)
  nlinarith [Real.sq_sqrt hL]

end LinearDistancePreservers.SphereRate

namespace LinearDistancePreservers.SphereRate

/-- The elementary-sphere logarithmic gain is exactly the gain of its
parameter-selected polynomial, after dividing by the terminal square. -/
theorem sphere_log_identity {d L s : ℝ} (hd : 3≤d) :
    logRatio d L ((2/3)*L-s) =
      ((2*d-2)/(d^2-2))*L+(((2*d+1)*(d-2)/(d^2-2))-2)*s := by
  have hD : d^2-2≠0 := by nlinarith
  unfold logRatio
  field_simp
  ring

/-- Compare the actual real-power polynomials, uniformly in the whole
large-dimension regime. -/
theorem polynomial_le_sphere {d N T : ℝ} (hd : 3≤d)
    (hN : 1≤N) (hT : 0<T) (hcap : Real.log T≤(2/3)*Real.log N)
    (hbudget : Real.sqrt (Real.log N)≤d^3) :
    N^(2/(d+1))*T^((2*d+1)*(d-1)/(d*(d+1))) ≤
      (N^((2*d-2)/(d^2-2))*T^((2*d+1)*(d-2)/(d^2-2)))*
        Real.exp (4*Real.sqrt (Real.log N)) := by
  have hN0 : 0<N := by linarith
  have hh := sharp_le_sphere_sqrt (by linarith : 2≤d)
    (Real.log_nonneg hN) (sub_nonneg.mpr hcap) hbudget
  rw [sub_sub_cancel,sphere_log_identity hd] at hh
  unfold TheoremFourRateAudit.logRatio at hh
  rw [Real.rpow_def_of_pos hN0,Real.rpow_def_of_pos hT,
    Real.rpow_def_of_pos hN0,Real.rpow_def_of_pos hT,← Real.exp_add,
    ← Real.exp_add,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

end LinearDistancePreservers.SphereRate

