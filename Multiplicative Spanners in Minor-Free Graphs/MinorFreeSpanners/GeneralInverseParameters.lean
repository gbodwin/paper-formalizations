import MinorFreeSpanners.GeneralIncrementParameters

namespace MinorFreeSpanners

/-- The concrete inverse-square and inverse-linear parameters satisfy all
actual star-growth and retained-minor hypotheses at every density above k³. -/
theorem general_inverse_parameters (k : ℕ) (d : ℝ)
    (hk : 16 ≤ k) (hd : (k:ℝ)^3 ≤ d) :
    1 ≤ d ∧ 0 ≤ 1/(k:ℝ)^2 ∧ 1/(k:ℝ)^2 ≤ 1 ∧
      0 ≤ 1/(k:ℝ) ∧ 1 ≤ (1/(k:ℝ))*d ∧
      (k:ℝ) ≤ (1/(k:ℝ)^2)*d ∧
      (3*(1/(k:ℝ)^2)+4*(1/(k:ℝ)))*(k:ℝ) ≤ 5 := by
  have hkR : (16:ℝ) ≤ k := by exact_mod_cast hk
  have hp : (0:ℝ) < k := by linarith
  have hs : (1:ℝ) ≤ (k:ℝ)^2 := by nlinarith
  have hkd : (k:ℝ) ≤ d := by
    have h := mul_le_mul_of_nonneg_left hs hp.le
    nlinarith only [h,hd]
  refine ⟨by linarith,by positivity,?_,by positivity,?_,?_,?_⟩
  · exact (div_le_one (sq_pos_of_pos hp)).mpr hs
  · rw [one_div_mul_eq_div]
    exact (le_div_iff₀ hp).mpr (by simpa using hkd)
  · rw [one_div_mul_eq_div]
    apply (le_div_iff₀ (sq_pos_of_pos hp)).mpr
    nlinarith only [hd]
  · apply residual_loss_coefficient (k:ℝ) (1/(k:ℝ)^2) (1/(k:ℝ)) (by linarith)
    · exact le_of_eq (one_div_mul_cancel (ne_of_gt (sq_pos_of_pos hp)))
    · exact le_of_eq (one_div_mul_cancel (ne_of_gt hp))

/-- Convert the actual absolute dense-witness edge guarantee into the
common density scale used by the real bipartite branch. -/
theorem absolute_dense_witness_ratio (k d n e : ℝ) (hk : 0 < k) (hd : 0 < d)
    (hn : n ≤ 12*k^4*d) (he : d^2/(2*k^3) ≤ e) :
    0 < e ∧ d/(800000*k^7)*n ≤ e := by
  have hp : 0 < 2*k^3 := by positivity
  have hepos : 0 < e := lt_of_lt_of_le (by positivity) he
  have he' : d^2 ≤ e*(2*k^3) := (div_le_iff₀ hp).mp he
  have h1 := mul_le_mul_of_nonneg_left hn hd.le
  have h2 := mul_le_mul_of_nonneg_left he' (show 0 ≤ 12*k^4 by positivity)
  have h3 : 0 ≤ (800000-24)*k^7*e := by positivity
  refine ⟨hepos,?_⟩
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (show 0 < 800000*k^7 by positivity)).mpr
  nlinarith only [h1,h2,h3]

/-- Enlarging the fixed polynomial denominator preserves the bipartite
positive-density guarantee for every k>=1. -/
theorem bipartite_density_denominator (k d : ℝ) (hk : 1 ≤ k) (hd : 0 ≤ d) :
    d/(800000*k^7) ≤ d/(800000*k^5) := by
  have hp : 0 < k := by linarith
  have hs : 1 ≤ k^2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ 800000*k^5 by positivity)
  have hden : 800000*k^5 ≤ 800000*k^7 := by nlinarith only [hm]
  exact div_le_div_of_nonneg_left hd (by positivity) hden

end MinorFreeSpanners
