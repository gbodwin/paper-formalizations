import MinorFreeSpanners.CanonicalPhaseParameterChoice

/-! The phase girth target fits the corrected greedy weighted-girth threshold.
The factor is `(1 + eps) * (2*r - 1) + 1`; no stronger `2*r` threshold
is assumed. The integral multiplier can be selected with `4000 ≤ t * eps`. -/
namespace MinorFreeSpanners

 theorem canonical_girth_below_corrected_threshold (t r : ℕ) (eps : ℝ)
    (ht : 1≤t) (hr : 1≤r) (hscale : 4000≤(t:ℝ)*eps) :
    2*(r:ℝ)*(1+2000/(t:ℝ))≤(1+eps)*(2*(r:ℝ)-1)+1 := by
  have htR : (1:ℝ)≤t := by exact_mod_cast ht
  have hrR : (1:ℝ)≤r := by exact_mod_cast hr
  have htpos : (0:ℝ)<t := by linarith
  have heps : 0≤eps := by nlinarith only [hscale,htpos]
  have hdiv : (4000:ℝ)/(t:ℝ)≤eps := by
    apply (div_le_iff₀ htpos).mpr
    nlinarith only [hscale]
  have hmul := mul_le_mul_of_nonneg_right hdiv (show (0:ℝ)≤r by positivity)
  have hwide := mul_nonneg heps (show (0:ℝ)≤(r:ℝ)-1 by linarith)
  have hid : 2*(r:ℝ)*(1+2000/(t:ℝ))=2*(r:ℝ)+(4000/(t:ℝ))*(r:ℝ) := by ring
  rw [hid]
  nlinarith only [hmul,hwide]

end MinorFreeSpanners
