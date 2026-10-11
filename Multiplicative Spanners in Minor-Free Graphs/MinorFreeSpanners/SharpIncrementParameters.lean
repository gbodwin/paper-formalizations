import MinorFreeSpanners.GeneralIncrementParameters

/-! Preserve the near-equality between actual branch width and density gain.
The ceiling is legal because the destination degree is an integer. -/
namespace MinorFreeSpanners

theorem sharp_increment_degree (k : ℕ) (d : ℝ)
    (hk : 32 ≤ k) (hd : (k:ℝ)^3 ≤ d) :
    let F : ℝ := d-(2+3*(k:ℝ))*(1/(k:ℝ)^2)*d
    let D : ℕ := ⌈F⌉₊
    (k:ℝ) ≤ D ∧ d/2 ≤ (D:ℝ) ∧ (D:ℝ) ≤ d ∧ F ≤ (D:ℝ) := by
  have hkR : (32:ℝ) ≤ k := by exact_mod_cast hk
  have hp : (0:ℝ)<k := by linarith
  have hdpos : 0<d := lt_of_lt_of_le (by positivity : (0:ℝ)<(k:ℝ)^3) hd
  have hquarter : (2+3*(k:ℝ))*(1/(k:ℝ)^2) ≤ 1/4 := by
    rw [mul_one_div]
    apply (div_le_iff₀ (sq_pos_of_pos hp)).mpr
    nlinarith
  have hscale := mul_le_mul_of_nonneg_right hquarter hdpos.le
  have hdiv : (k:ℝ) ≤ d/(k:ℝ)^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hp)).mpr
    nlinarith only [hd]
  have hloss : 1 ≤ (2+3*(k:ℝ))*(1/(k:ℝ)^2)*d := by
    have hh := mul_le_mul_of_nonneg_left hdiv (show 0≤2+3*(k:ℝ) by positivity)
    have he : (2+3*(k:ℝ))*(d/(k:ℝ)^2)=(2+3*(k:ℝ))*(1/(k:ℝ)^2)*d := by ring
    rw [he] at hh
    nlinarith only [hh,hkR]
  have hdk : 2*(k:ℝ) ≤ d := by
    have hsq : 2 ≤ (k:ℝ)^2 := by nlinarith
    nlinarith [mul_nonneg hp.le (sub_nonneg.mpr hsq)]
  have hlo := Nat.le_ceil (d-(2+3*(k:ℝ))*(1/(k:ℝ)^2)*d)
  have hhi := Nat.ceil_lt_add_one (show 0 ≤ d-(2+3*(k:ℝ))*(1/(k:ℝ)^2)*d by linarith)
  exact ⟨by linarith,by linarith,by linarith,hlo⟩

theorem sharp_increment_factor (k : ℕ) (d D : ℝ)
    (hk : 32 ≤ k) (hd : 0 ≤ d)
    (hD : d-(2+3*(k:ℝ))*(1/(k:ℝ)^2)*d ≤ D) :
    ((k/4+1:ℕ):ℝ)*(1-16/(k:ℝ))*d ≤ ((k/4:ℕ)-1)*D := by
  have hkR : (32:ℝ) ≤ k := by exact_mod_cast hk
  have hp : (0:ℝ)<k := by linarith
  have hmod := Nat.mod_lt k (show 0<4 by omega)
  have hdiv := Nat.div_add_mod k 4
  have hmNat : k ≤ 4*(k/4+1) := by omega
  have hm : (k:ℝ) ≤ 4*((k/4+1:ℕ):ℝ) := by exact_mod_cast hmNat
  have hl : (k/4:ℕ) ≤ (k:ℝ)/4 := by
    have hh : 4*(k/4) ≤ k := by omega
    have hhR : 4*(k/4:ℕ) ≤ (k:ℝ) := by exact_mod_cast hh
    linarith
  have hlpos : (0:ℝ) ≤ (k/4:ℕ)-1 := by
    have hh : 1 ≤ k/4 := by omega
    have hhR : (1:ℝ) ≤ (k/4:ℕ) := by exact_mod_cast hh
    linarith
  have hepos : 0 ≤ (2+3*(k:ℝ))*(1/(k:ℝ)^2) := by positivity
  have he : (2+3*(k:ℝ))*(1/(k:ℝ)^2) ≤ 4/(k:ℝ) := by
    rw [mul_one_div]
    apply (div_le_div_iff₀ (sq_pos_of_pos hp) hp).mpr
    nlinarith
  have hprod := mul_le_mul (show (k/4:ℕ)-1 ≤ (k:ℝ)/4 by linarith) he hepos (by positivity : 0≤(k:ℝ)/4)
  have hloss : ((k/4:ℕ)-1)*((2+3*(k:ℝ))*(1/(k:ℝ)^2)) ≤ 1 := by
    have heq : ((k:ℝ)/4)*(4/(k:ℝ))=1 := by field_simp
    rwa [heq] at hprod
  have hgain : 4 ≤ ((k/4+1:ℕ):ℝ)*(16/(k:ℝ)) := by
    have hx : 4 ≤ (16*((k/4+1:ℕ):ℝ))/(k:ℝ) :=
      (le_div_iff₀ hp).mpr (by nlinarith only [hm])
    simpa only [mul_div_assoc,mul_comm] using hx
  have hcoef : ((k/4+1:ℕ):ℝ)*(1-16/(k:ℝ)) ≤
      ((k/4:ℕ)-1)*(1-(2+3*(k:ℝ))*(1/(k:ℝ)^2)) := by
    push_cast at hgain ⊢
    nlinarith only [hgain,hloss]
  have h1 := mul_le_mul_of_nonneg_right hcoef hd
  have h2 := mul_le_mul_of_nonneg_left hD hlpos
  nlinarith only [h1,h2]

end MinorFreeSpanners
