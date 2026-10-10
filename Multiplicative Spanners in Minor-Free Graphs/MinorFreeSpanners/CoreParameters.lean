import MinorFreeSpanners.DensityAlgebra
import Mathlib.Data.Nat.Choose.Cast

namespace MinorFreeSpanners

/-- Explicit rounding for the high-girth lower-bound core. -/
theorem core_parameter_bounds (k h N : ℕ) (c a : ℝ)
    (hk : 1 ≤ k) (hh : 3 ≤ h) (hN : N ≤ h)
    (ha : 0 < a) (hac : a ≤ c) (ha8 : a ≤ 1/8)
    (hlarge : 2/a ≤ h) :
    let β := 2*(k:ℝ)/(k+1)
    let v := ⌈(h:ℝ)^β⌉₊
    let m := ⌊a*(h:ℝ)^2⌋₊
    0 < v ∧ N ≤ v ∧
    (v:ℝ) ≤ 2*(h:ℝ)^β ∧
    a/2*(h:ℝ)^2 ≤ m ∧ (m:ℝ) ≤ c*(v:ℝ)^(((k:ℝ)+1)/k) ∧
    m < h.choose 2 := by
  let β := 2*(k:ℝ)/(k+1)
  let v := ⌈(h:ℝ)^β⌉₊
  let m := ⌊a*(h:ℝ)^2⌋₊
  have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0:ℝ) < k := by linarith
  have hhR : (3:ℝ) ≤ h := by exact_mod_cast hh
  have hh1 : (1:ℝ) ≤ h := by linarith
  have hβ : 1 ≤ β := by dsimp [β]; apply (le_div_iff₀ (by positivity)).mpr; linarith
  have hp : (h:ℝ) ≤ (h:ℝ)^β := Real.self_le_rpow_of_one_le hh1 hβ
  have hvlo : (h:ℝ)^β ≤ v := Nat.le_ceil _
  have hvNat : h ≤ v := by exact_mod_cast hp.trans hvlo
  have hvpos : 0 < v := by omega
  have hvupper : (v:ℝ) ≤ 2*(h:ℝ)^β := by
    have ht := Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg h) β)
    change (v:ℝ) < (h:ℝ)^β+1 at ht
    linarith
  have hprod : 2 ≤ a*(h:ℝ) := by nlinarith [(div_le_iff₀ ha).mp hlarge]
  have harg : 2 ≤ a*(h:ℝ)^2 := by
    have hh := mul_le_mul_of_nonneg_left hh1 (show 0 ≤ a*(h:ℝ) by positivity)
    nlinarith
  have hfloor := Nat.lt_floor_add_one (a*(h:ℝ)^2)
  have hmlo : a/2*(h:ℝ)^2 ≤ m := by dsimp [m]; nlinarith
  have hmhi : (m:ℝ) ≤ a*(h:ℝ)^2 := Nat.floor_le (by positivity)
  have halpha : 0 ≤ ((k:ℝ)+1)/k := by positivity
  have hpower : (h:ℝ)^2 ≤ (v:ℝ)^(((k:ℝ)+1)/k) := by
    have hr := Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg h) β) hvlo halpha
    have hmul : β*(((k:ℝ)+1)/k) = 2 := by dsimp [β]; field_simp [hk0.ne'] <;> ring
    rw [← Real.rpow_mul (Nat.cast_nonneg h),hmul,Real.rpow_two] at hr
    exact hr
  have hcm : (m:ℝ) ≤ c*(v:ℝ)^(((k:ℝ)+1)/k) :=
    hmhi.trans ((mul_le_mul_of_nonneg_right hac (sq_nonneg (h:ℝ))).trans
      (mul_le_mul_of_nonneg_left hpower (ha.le.trans hac)))
  have hchoose : (m:ℝ) < (h.choose 2:ℝ) := by
    rw [Nat.cast_choose_two]
    have hsm := mul_le_mul_of_nonneg_right ha8 (sq_nonneg (h:ℝ))
    nlinarith
  exact ⟨hvpos,hN.trans hvNat,hvupper,hmlo,hcm,Nat.cast_lt.mp hchoose⟩

/-- The rounded core retains the desired power of h in its edge density. -/
theorem core_density_bound (k h v m : ℕ) (a : ℝ)
    (hh : 0 < h) (hv : 0 < v) (ha : 0 ≤ a)
    (hvertices : (v:ℝ) ≤ 2*(h:ℝ)^(2*(k:ℝ)/(k+1)))
    (hedges : a/2*(h:ℝ)^2 ≤ m) :
    a/8*(h:ℝ)^(2/((k:ℝ)+1)) ≤ (m:ℝ)/(2*v) := by
  have hhR : (0:ℝ) < h := by exact_mod_cast hh
  have hvR : (0:ℝ) < v := by exact_mod_cast hv
  apply (le_div_iff₀ (by positivity : (0:ℝ) < 2*v)).mpr
  have hc : 0 ≤ a/8*(h:ℝ)^(2/((k:ℝ)+1)) := by positivity
  have hb := mul_le_mul_of_nonneg_left hvertices (show 0 ≤ 2*(a/8*(h:ℝ)^(2/((k:ℝ)+1))) by positivity)
  have he : (h:ℝ)^(2/((k:ℝ)+1)) * (h:ℝ)^(2*(k:ℝ)/(k+1)) = (h:ℝ)^2 := by
    rw [← Real.rpow_add hhR]
    have hex : 2/((k:ℝ)+1)+2*(k:ℝ)/(k+1) = 2 := by field_simp <;> ring
    rw [hex,Real.rpow_two]
  calc
    _ = (2*(a/8*(h:ℝ)^(2/((k:ℝ)+1))))*(v:ℝ) := by ring
    _ ≤ (2*(a/8*(h:ℝ)^(2/((k:ℝ)+1))))*(2*(h:ℝ)^(2*(k:ℝ)/(k+1))) := hb
    _ = a/2*((h:ℝ)^(2/((k:ℝ)+1))*(h:ℝ)^(2*(k:ℝ)/(k+1))) := by ring
    _ = a/2*(h:ℝ)^2 := by rw [he]
    _ ≤ _ := hedges

end MinorFreeSpanners
