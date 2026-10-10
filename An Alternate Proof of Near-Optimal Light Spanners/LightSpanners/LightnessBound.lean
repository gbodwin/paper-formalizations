import LightSpanners.SamplingCounting
import LightSpanners.CycleReduction

namespace LightSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V] {G T : SimpleGraph V} {w : Sym2 V → ℝ}

/-- Unit-cycle weight counting yields the lightness estimate with its explicit
constant baseline for unrestricted positive epsilon. -/
theorem UnitSpanningCycle.lightness_bound (C : UnitSpanningCycle G w)
    (hT : IsMinimumSpanningTree G T w) {eps : ℝ} {k : ℕ}
    (heps : 0<eps) (hk : 0<k)
    (hG : WeightedGirthAbove G w ((1+4*eps)*(2*k))) :
    lightness G T w≤2+16/eps*(Fintype.card V:ℝ)^((k:ℝ)⁻¹) := by
  have hnNat := C.three_le_card
  have hn : (3:ℝ)≤Fintype.card V := by exact_mod_cast hnNat
  have hb := C.unit_cycle_weight_bound heps hk hG
  rw [C.lightness_eq hT]
  apply (div_le_iff₀ (by linarith : 0<(Fintype.card V:ℝ)-1)).mpr
  have hp : 0≤(Fintype.card V:ℝ)^((k:ℝ)⁻¹) := Real.rpow_nonneg (by positivity) _
  have hcoef : 0≤8/eps*(Fintype.card V:ℝ)^((k:ℝ)⁻¹) := by positivity
  have hprod := mul_nonneg (show 0≤(Fintype.card V:ℝ)-2 by linarith) hcoef
  simp only [div_eq_mul_inv] at hb hcoef hprod ⊢
  nlinarith

/-- Applying the complete actual-graph reduction removes the unit-cycle premise. -/
theorem weighted_girth_lightness_bound (hT : IsMinimumSpanningTree G T w)
    (hw : ∀ e∈G.edgeSet,0<w e) {eps : ℝ} {k : ℕ}
    (heps : 0<eps) (hk : 0<k)
    (hG : WeightedGirthAbove G w ((1+4*eps)*(2*k))) :
    lightness G T w≤8+256/eps*(Fintype.card V:ℝ)^((k:ℝ)⁻¹) := by
  by_cases hforest : G.IsAcyclic
  · have htree : G.IsTree := ⟨hT.2.1.connected.mono hT.1,hforest⟩
    have hGT : G≤T := (isTree_iff_minimal_connected.mp htree).2 hT.2.1.connected hT.1
    have heq : G=T := le_antisymm hGT hT.1
    rw [heq,lightness]
    have hh : totalWeight T w/totalWeight T w≤1 := div_self_le_one _
    have hp : 0≤256/eps*(Fintype.card V:ℝ)^((k:ℝ)⁻¹) := by positivity
    linarith
  · obtain ⟨n,H,S,w',hS,⟨C⟩,hH,hcard,htransfer⟩ :=
      unit_spanning_cycle_reduction_of_mst w ((1+4*eps)*(2*k)) (by positivity) hT hw hG hforest
    have hbound := C.lightness_bound hS heps hk hH
    have hkR : (1:ℝ)≤k := by exact_mod_cast hk
    have hr0 : 0≤(k:ℝ)⁻¹ := by positivity
    have hr1 : (k:ℝ)⁻¹≤1 := inv_le_one_of_one_le₀ hkR
    have hn : (n:ℝ)≤4*(Fintype.card V:ℝ) := by
      exact_mod_cast (show n≤4*Fintype.card V by omega)
    have hroot : (n:ℝ)^((k:ℝ)⁻¹)≤4*(Fintype.card V:ℝ)^((k:ℝ)⁻¹) := by
      calc
        _ ≤ (4*(Fintype.card V:ℝ))^((k:ℝ)⁻¹) := Real.rpow_le_rpow (by positivity) hn hr0
        _ = (4:ℝ)^((k:ℝ)⁻¹)*(Fintype.card V:ℝ)^((k:ℝ)⁻¹) := Real.mul_rpow (by norm_num) (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_right (Real.rpow_le_self_of_one_le (by norm_num) hr1)
          (Real.rpow_nonneg (by positivity) _)
    simp only [Fintype.card_fin] at hbound
    have hm := mul_le_mul_of_nonneg_left hroot (by positivity : 0≤16/eps)
    simp only [div_eq_mul_inv] at hbound hm ⊢
    nlinarith

end LightSpanners
