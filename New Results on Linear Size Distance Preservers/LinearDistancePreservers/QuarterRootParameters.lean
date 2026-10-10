import LinearDistancePreservers.TheoremFourRateAudit

namespace LinearDistancePreservers.TheoremFourGeneral

/-- The fourth-root dimension automatically lies in the elementary-sphere
regime, with useful explicit floor bounds. -/
theorem quarter_root_dimension {R : ℝ} (hR : 8≤R) :
    ∃ d : ℕ, 3≤d ∧ R/2≤(d : ℝ) ∧ (d : ℝ)≤R ∧
      R^2≤(d : ℝ)^3 ∧ (d : ℝ)≤R^2 := by
  let d := ⌊R⌋₊
  have hR0 : 0≤R := by linarith
  have hdu : (d : ℝ)≤R := Nat.floor_le hR0
  have hdl : R<(d : ℝ)+1 := Nat.lt_floor_add_one _
  have hd3 : (3 : ℝ)≤d := by linarith
  have hdN : 3≤d := by exact_mod_cast hd3
  have hround : R/2≤(d : ℝ) := by linarith
  have hc := pow_le_pow_left₀ (by positivity : (0 : ℝ)≤R/2) hround 3
  have hr := mul_le_mul_of_nonneg_right hR (sq_nonneg R)
  have hsmall : R^2≤(d : ℝ)^3 := by nlinarith only [hc,hr]
  have hupper : (d : ℝ)≤R^2 := by nlinarith only [hdu,hR]
  exact ⟨d,hdN,hround,hdu,hsmall,hupper⟩

/-- A logarithmic terminal deficit32R³ pays the full sphere construction
loss15R² and retains another R² of superquadratic gain. -/
theorem quarter_root_gain {R d t : ℝ} (hR : 8≤R) (hd : 3≤d)
    (hlo : R/2≤d) (hup : d≤R) (ht : 32*R^3≤t) :
    16*R^2≤TheoremFourRateAudit.logRatio d (R^4) ((2/3)*R^4-t) := by
  have hR0 : 0≤R := by linarith
  have hd0 : 0<d := by linarith
  have ht0 : 0≤t := (by positivity : 0≤32*R^3).trans ht
  have hprod := mul_le_mul (show (3/2)*R≤3*d+1 by linarith) ht
    (by positivity : 0≤32*R^3) (by positivity : 0≤3*d+1)
  have hden : d*(d+1)≤2*R^2 := by
    have hh := mul_le_mul hup (show d+1≤2*R by linarith) (by linarith : 0≤d+1) hR0
    nlinarith only [hh]
  have hh := mul_le_mul_of_nonneg_left hden (by positivity : 0≤16*R^2)
  rw [TheoremFourRateAudit.deficit_identity (by linarith : 1≤d)]
  apply (le_div_iff₀ (by positivity : 0<d*(d+1))).mpr
  have hr4 := pow_nonneg hR0 4
  nlinarith only [hprod,hh,hr4]

end LinearDistancePreservers.TheoremFourGeneral
