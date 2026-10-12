import MinorFreeSpanners.GreedyMinorLightness
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! An explicit universal coefficient separates the inverse-slack and
polylogarithmic minor-order factors from the constructed lightness bound. -/
namespace MinorFreeSpanners

noncomputable def minorLightnessConstant : ℝ :=
  2*43*30008*8097^3*(1600000*(131104:ℝ)^7*24576^2+2*(131104:ℝ)^3)

 theorem constructed_coefficient_bound (eps : ℝ) (heps : 0<eps) (heps1 : eps≤1)
    (r h : ℕ) (hh : 1≤h) :
    2*(42*(Nat.log 2 (canonicalScale eps)+1:ℕ)+1)*canonicalPhaseCredit (canonicalScale eps) r h≤
      minorLightnessConstant*(Real.logb 2 (8097/eps)+1)*
        (Nat.log 2 h+2:ℕ)^9*(h:ℝ)^(2/(r+1:ℝ))/eps^3 := by
  let t := canonicalScale eps
  let A : ℝ := 1600000*(131104:ℝ)^7*24576^2+2*(131104:ℝ)^3
  let H : ℝ := (Nat.log 2 h+2:ℕ)
  let z : ℝ := (h:ℝ)^(2/(r+1:ℝ))
  have hA : 1≤A := by norm_num [A]
  have hH : 1≤H := by dsimp [H]; exact_mod_cast (show 1≤Nat.log 2 h+2 by omega)
  have hz : 1≤z := Real.one_le_rpow (by exact_mod_cast hh) (by positivity)
  have hH9 : 1≤H^9 := one_le_pow₀ hH
  have hP : 1≤A*H^9 := one_le_mul_of_one_le_of_one_le hA hH9
  have hPz : 1≤A*H^9*z := one_le_mul_of_one_le_of_one_le hP hz
  have hmax : max 1 (fullDensityLoss h*z)≤A*H^9*z := by
    apply max_le hPz
    exact mul_le_mul_of_nonneg_right (fullDensityLoss_polylog h (by omega)) (by linarith)
  obtain ⟨ht,_,htupper⟩ := canonicalScale_bounds eps heps heps1
  have htpos : (0:ℝ)<t := by dsimp [t]; exact_mod_cast (show 0<canonicalScale eps by omega)
  have hlogs : (Nat.log 2 t:ℝ)≤Real.logb 2 (8097/eps) :=
    (Real.natLog_le_logb t 2).trans (Real.logb_le_logb_of_le (by norm_num) htpos htupper)
  have hlog : 0≤Real.logb 2 (8097/eps) := (Nat.cast_nonneg (Nat.log 2 t)).trans hlogs
  have hfactor : 2*(42*(Nat.log 2 t+1:ℕ)+1:ℝ)≤2*43*(Real.logb 2 (8097/eps)+1) := by
    push_cast
    nlinarith only [hlogs,hlog]
  have hcredit : canonicalPhaseCredit t r h≤30008*(A*H^9*z)*(8097/eps)^3 := by
    unfold canonicalPhaseCredit
    change 30008*max 1 (fullDensityLoss h*z)*(t:ℝ)^3≤_
    have hm0 : 0≤max 1 (fullDensityLoss h*z) := le_trans (by norm_num) (le_max_left _ _)
    have hp := pow_le_pow_left₀ htpos.le htupper 3
    exact mul_le_mul (mul_le_mul_of_nonneg_left hmax (by norm_num)) hp (by positivity) (by positivity)
  have hc0 : 0≤canonicalPhaseCredit t r h := by unfold canonicalPhaseCredit; positivity
  have hb := mul_le_mul hfactor hcredit hc0 (by positivity)
  change 2*(42*(Nat.log 2 t+1:ℕ)+1)*canonicalPhaseCredit t r h≤_
  refine hb.trans_eq ?_
  dsimp [minorLightnessConstant,A,H,z]
  field_simp

end MinorFreeSpanners
