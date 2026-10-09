import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Audit of the last asymptotic implication in Theorem 4.
These are bounds on the paper's displayed expression, NOT upper bounds
on the edges needed by a preserver. They identify why the displayed
lower bound, with a uniform exp(-c sqrt(log N)) loss, does not establish
its stated near-N^(2/3) superquadratic corollary. They do not refute the
existential graph theorem, which could have a stronger proof. -/
namespace LinearDistancePreservers.TheoremFourRateAudit

/-- Logarithm of the displayed polynomial factor divided by sigma²,
where L=log N and s=log sigma. -/
noncomputable def logRatio (d L s : ℝ) : ℝ :=
  2/(d+1)*L + ((2*d+1)*(d-1)/(d*(d+1))-2)*s

/-- The connection to the actual powers in the printed bound, rather
than just an abstract algebraic expression in logarithmic variables. -/
theorem log_polynomial_ratio {N sigma d : ℝ} (hN : 0 < N) (hs : 0 < sigma) :
    Real.log (N^(2/(d+1))*sigma^((2*d+1)*(d-1)/(d*(d+1)))/sigma^2) =
      logRatio d (Real.log N) (Real.log sigma) := by
  rw [Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),Real.log_rpow hN,
    Real.log_rpow hs,Real.log_pow]
  unfold logRatio
  ring

theorem deficit_identity {d L t : ℝ} (hd : 1 ≤ d) :
    logRatio d L ((2/3)*L-t) = ((3*d+1)*t-(2/3)*L)/(d*(d+1)) := by
  have h0 : d ≠ 0 := by linarith
  have h1 : d+1 ≠ 0 := by linarith
  unfold logRatio
  field_simp
  ring

/-- Uniform in the dimension, even before restricting d≤O(sqrt L). -/
theorem logRatio_le {d L t : ℝ} (hd : 1 ≤ d) (hL : 0 < L) :
    logRatio d L ((2/3)*L-t) ≤ 27*t^2/(8*L) := by
  rw [deficit_identity hd]
  apply (div_le_div_iff₀ (by positivity : 0 < d*(d+1)) (by positivity : 0 < 8*L)).mpr
  have hs := sq_nonneg (4*L-3*(3*d+1)*t)
  have ht := mul_nonneg (show 0 ≤ 3*d-1 by linarith) (sq_nonneg t)
  nlinarith

/-- An O(sqrt(log N)) deficit below N^(2/3) gives only a constant
polynomial-factor gain, uniformly over every allowed dimension. -/
theorem sqrt_deficit_le {d L t K : ℝ}
    (hd : 1 ≤ d) (hL : 0 < L) (ht : 0 ≤ t) (hK : 0 ≤ K)
    (hdeficit : t ≤ K*Real.sqrt L) :
    logRatio d L ((2/3)*L-t) ≤ 27*K^2/8 := by
  apply (logRatio_le hd hL).trans
  have hs := Real.sq_sqrt hL.le
  have hsq : t^2 ≤ K^2*L := by
    nlinarith [sq_nonneg (K*Real.sqrt L-t),
      mul_nonneg (sub_nonneg.mpr hdeficit) (show 0 ≤ K*Real.sqrt L+t by positivity)]
  apply (div_le_iff₀ (by positivity : 0 < 8*L)).mpr
  nlinarith

/-- Including a fixed positive square-root exponential loss does not
make the displayed ratio superquadratic. The right side tends to zero
as L grows, for fixed K and positive c. No graph upper bound is asserted. -/
theorem suppressed_ratio_le {d L t K c : ℝ}
    (hd : 1 ≤ d) (hL : 0 < L) (ht : 0 ≤ t) (hK : 0 ≤ K)
    (hdeficit : t ≤ K*Real.sqrt L) :
    Real.exp (logRatio d L ((2/3)*L-t)-c*Real.sqrt L) ≤
      Real.exp (27*K^2/8-c*Real.sqrt L) := by
  apply Real.exp_le_exp.mpr
  exact sub_le_sub_right (sqrt_deficit_le hd hL ht hK hdeficit) _

/-- Pointwise bound on the literal expression in Theorem 4 after a
uniform exponential loss, divided by sigma². It is an upper bound on
that LOWER-BOUND EXPRESSION, not an upper bound on graph edge counts. -/
theorem suppressed_expression_le {N sigma d t K c : ℝ}
    (hN : 1 < N) (hs : 0 < sigma) (hd : 1 ≤ d) (ht : 0 ≤ t) (hK : 0 ≤ K)
    (hsigma : Real.log sigma = (2/3)*Real.log N-t)
    (hdeficit : t ≤ K*Real.sqrt (Real.log N)) :
    (N^(2/(d+1))*sigma^((2*d+1)*(d-1)/(d*(d+1)))/sigma^2) *
      Real.exp (-c*Real.sqrt (Real.log N)) ≤
      Real.exp (27*K^2/8-c*Real.sqrt (Real.log N)) := by
  have hN0 : 0 < N := lt_trans zero_lt_one hN
  have hpos : 0 < N^(2/(d+1))*sigma^((2*d+1)*(d-1)/(d*(d+1)))/sigma^2 := by
    positivity
  rw [← Real.exp_log hpos,log_polynomial_ratio hN0 hs,← Real.exp_add,hsigma]
  simpa only [sub_eq_add_neg,neg_mul] using
    (suppressed_ratio_le hd (Real.log_pos hN) ht hK hdeficit (c := c))

end LinearDistancePreservers.TheoremFourRateAudit
