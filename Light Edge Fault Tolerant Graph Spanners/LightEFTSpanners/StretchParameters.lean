import LightSpanners.MainTheorem

/-! Exact stretch/weighted-girth substitution. The paper's larger displayed
threshold cannot be inferred from the smaller actual threshold. The explicit
coarse bound below is an actual graph theorem, without a lambda oracle. -/
namespace LightEFTSpanners
open SimpleGraph LightSpanners
attribute [local instance] Classical.propDecidable

theorem stretch_threshold_gap (eps : ℝ) (k : ℕ) :
    (1+eps)*(2*k) - ((1+eps)*(2*k-1)+1) = eps := by ring

theorem actual_threshold_lt_printed {eps : ℝ} (heps : 0 < eps) (k : ℕ) :
    (1+eps)*(2*k-1)+1 < (1+eps)*(2*k) := by
  linarith [stretch_threshold_gap eps k]

/-- The coarse polynomial dependence survives the corrected substitution;
the additive constant also keeps the estimate valid for unrestricted epsilon. -/
theorem corrected_threshold_lightness {V : Type*} [Fintype V] [DecidableEq V]
    {G T : SimpleGraph V} {w : Sym2 V → ℝ}
    (hT : IsMinimumSpanningTree G T w) (hw : ∀ e∈G.edgeSet,0<w e)
    {eps : ℝ} {k : ℕ} (heps : 0<eps) (hk : 0<k)
    (hG : WeightedGirthAbove G w ((1+eps)*(2*k-1)+1)) :
    lightness G T w ≤ 8+2048/eps*(Fintype.card V:ℝ)^((k:ℝ)⁻¹) := by
  have hkR : (1:ℝ)≤k := by exact_mod_cast hk
  have hkpos : (0:ℝ)<k := by exact_mod_cast hk
  have hterm : (0:ℝ)<2*k-1 := by linarith
  let δ : ℝ := eps*(2*k-1)/(8*k)
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hδlower : eps/8≤δ := by
    apply (le_div_iff₀ (by positivity : 0<(8:ℝ)*k)).mpr
    nlinarith [mul_pos heps hkpos]
  have hthreshold : (1+4*δ)*(2*k)=(1+eps)*(2*k-1)+1 :=
    stretch_reparameterization eps k hk
  have hG' : WeightedGirthAbove G w ((1+4*δ)*(2*k)) := by rwa [hthreshold]
  have hb := weighted_girth_lightness_bound hT hw hδ hk hG'
  have hcoef : 256/δ≤2048/eps := (div_le_div_iff₀ hδ heps).mpr (by nlinarith)
  have hm := mul_le_mul_of_nonneg_right hcoef
    (Real.rpow_nonneg (by positivity : (0:ℝ)≤Fintype.card V) ((k:ℝ)⁻¹))
  linarith
end LightEFTSpanners
