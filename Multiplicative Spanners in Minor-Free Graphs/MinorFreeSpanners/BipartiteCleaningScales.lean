import MinorFreeSpanners.CleaningScales

/-! The separate bipartite numerical domain for the proved cleaning
alternative. This does not complete the density-increment/asymptotic join. -/
namespace MinorFreeSpanners

/-- The lower common-neighbor threshold is an inverse-quadratic scale; the
relation needed by the actual switch witness is checked explicitly. -/
theorem bipartite_cleaning_scale_threshold (k ell d : ℝ) (hk : 0 < k)
    (hellk : 4*ell ≤ k) (hd : 0 ≤ d) :
    4*ell*(d/(100*k^2)) ≤ d/(100*k) := by
  have hk0 : k≠0 := ne_of_gt hk
  have hq : d/(100*k^2)=(d/(100*k))/k := by field_simp
  rw [hq]
  have hr : 0 ≤ (d/(100*k))/k := by positivity
  have h := mul_le_mul_of_nonneg_right hellk hr
  have he : k*((d/(100*k))/k)=d/(100*k) := by field_simp
  rw [he] at h
  exact h

/-- For d>=k and ell>=1, the full real edge-loss coefficient, with the
safe upper bound ell² on the natural collision factor, is at most2ell*d/k. -/
theorem bipartite_cleaning_scale_loss (k ell d : ℝ) (hk : 0 < k)
    (hell : 1 ≤ ell) (hellk : 4*ell ≤ k) (hd : k ≤ d) :
    ell+4*ell^2*(d/(100*k^2))+(ell+1)*(d/(100*k))+ell*(d/(100*k)) ≤
      2*ell*d/k := by
  have hk0 : k≠0 := ne_of_gt hk
  have hk2 : 0 < k := hk
  have hd0 : 0 ≤ d := hk.le.trans hd
  have hell0 : 0 ≤ ell := by linarith
  let t := ell*d/k
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have hbase : ell ≤ t := by
    apply (le_div_iff₀ hk2).mpr
    nlinarith [mul_nonneg hell0 (sub_nonneg.mpr hd)]
  have hratio : 4*ell/k ≤ 1 := (div_le_one hk).mpr hellk
  have hcollision_eq : 4*ell^2*(d/(100*k^2))=(4*ell/k)*(t/100) := by
    dsimp [t]
    field_simp
  have hcollision : 4*ell^2*(d/(100*k^2)) ≤ t/100 := by
    rw [hcollision_eq]
    exact (mul_le_mul_of_nonneg_right hratio (by positivity)).trans_eq (one_mul _)
  have hmated : (ell+1)*(d/(100*k))+ell*(d/(100*k)) ≤ 3*t/100 := by
    have hr0 : 0 ≤ d/(100*k) := by positivity
    have h := mul_le_mul_of_nonneg_right (show 2*ell+1 ≤ 3*ell by linarith) hr0
    have he : 3*ell*(d/(100*k))=3*t/100 := by dsimp [t]; ring
    rw [he] at h
    nlinarith
  have he : 2*ell*d/k=2*t := by dsimp [t]; ring
  rw [he]
  linarith

end MinorFreeSpanners

namespace MinorFreeSpanners

/-- The actual natural collision factor is bounded, rather than silently
replaced by a real subtraction at ell=0. -/
theorem bipartite_cleaning_scale_nat_loss (k d : ℝ) (ell : ℕ) (hk : 0 < k)
    (hell : 1 ≤ ell) (hellk : 4*(ell:ℝ) ≤ k) (hd : k ≤ d) :
    (ell:ℝ)+4*((ell*(ell-1):ℕ):ℝ)*((1/(100*k^2))*d)+
      (ell+1)*(1/(100*k))*d+ell*(d/(100*k)) ≤ 2*ell*d/k := by
  have he : (1:ℝ) ≤ ell := by exact_mod_cast hell
  have hcN : ell*(ell-1) ≤ ell*ell := Nat.mul_le_mul_left ell (Nat.sub_le _ _)
  have hc : ((ell*(ell-1):ℕ):ℝ) ≤ (ell:ℝ)^2 := by
    norm_num only [pow_two]
    exact_mod_cast hcN
  have hq : 0 ≤ (1/(100*k^2))*d := by
    have : 0 ≤ d := hk.le.trans hd
    positivity
  have h := mul_le_mul_of_nonneg_right hc hq
  have hs := bipartite_cleaning_scale_loss k ell d hk he hellk hd
  have heq : (1/(100*k^2))*d=d/(100*k^2) := by ring
  have heq2 : (ell+1)*(1/(100*k))*d=(ell+1)*(d/(100*k)) := by ring
  rw [heq,heq2]
  rw [heq] at h
  linarith

/-- The genuine small-dense alternative has an explicit inverse-fifth
power density on these scales. This numerical lemma does not supply H. -/
theorem bipartite_cleaning_dense_scale (k ell d D n e : ℝ) (hk : 0 < k)
    (hell : 1 ≤ ell) (hellk : 4*ell ≤ k) (hd : 0 ≤ d) (hD0 : 0 ≤ D)
    (hD : D ≤ 5*k^2*d) (hn : n ≤ 2*(ell+1)*D)
    (he : (d/(100*k))^2 ≤ 4*e) :
    n ≤ 10*k^3*d ∧ d/(400000*k^5)*n ≤ e := by
  have hk0 : k≠0 := ne_of_gt hk
  have hk6 : 0 < k^5 := pow_pos hk 5
  have hell' : ell+1 ≤ k := by linarith
  have hDn : 2*(ell+1)*D ≤ 2*k*D := by nlinarith
  have hn' : n ≤ 10*k^3*d := by
    have hm := mul_le_mul_of_nonneg_left hD (show 0 ≤ 2*k by positivity)
    nlinarith
  have hsq := mul_le_mul_of_nonneg_left he (sq_nonneg (100*k))
  have hid : (100*k)^2*(d/(100*k))^2=d^2 := by field_simp
  rw [hid] at hsq
  have hr : d^2 ≤ 40000*k^2*e := by nlinarith [hsq]
  refine ⟨hn',?_⟩
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (show 0 < 400000*k^5 by positivity)).mpr
  have hm := mul_le_mul_of_nonneg_left hn' hd
  have hm2 := mul_le_mul_of_nonneg_left hr (show 0 ≤ 10*k^3 by positivity)
  nlinarith [hm,hm2]

end MinorFreeSpanners
