import LightEFTSpanners.ExtremalLightnessSpectrum
import LightEFTSpanners.HostLocalBlocking

namespace LightEFTSpanners
open SimpleGraph Finset LightSpanners
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

 theorem actual_threshold_gt_two {eps : ℝ} {k : ℕ} (heps : 0<eps) (hk : 0<k) :
    2<(1+eps)*(2*(k:ℝ)-1)+1 := by
  have hkR : (1:ℝ)≤k := by exact_mod_cast hk
  have hterm : 0<2*(k:ℝ)-1 := by linarith
  nlinarith [mul_pos heps hterm]

/-- Actual host pruning and sampling are bounded by the genuine extremal
supremum at stretch plus one, with no supplied extremal-lightness oracle. -/
theorem host_extremal_weight_bound {G T : SimpleGraph V} {seed U : Finset (Sym2 V)}
    {w : Sym2 V → ℝ} {eps : ℝ} {f k r : ℕ} {B : Sym2 V → Finset (Sym2 V)}
    (hB : BlockingData G seed w ((1+eps)*(2*k-1)) f B)
    (hT : T.IsTree) (hTG : T≤G) (hTseed : ∀ e∈T.edgeSet,e∈seed)
    (hUG : ∀ e∈U,e∈G.edgeSet) (hUseed : ∀ e∈U,e∉seed)
    (hhost : ∀ e∈U,Disjoint (B e) T.edgeFinset) (hcap : ∀ e∈U,(B e∩U).card≤r)
    (hw : ∀ e∈G.edgeSet,0<w e) (hr : 0<r) (hk : 0<k) (heps : 0<eps)
    (hn : 2≤Fintype.card V) :
    (∑ e∈U,w e) ≤ 4*(r:ℝ)*
      extremalLightness (Fintype.card V) ((1+eps)*(2*k-1)+1)*totalWeight T w := by
  have hXG : T⊔edgeGraph U≤G := sup_le hTG (by
    intro a b hab
    exact G.mem_edgeSet.mp (hUG _ ((mem_edgeGraph U _).mp ((edgeGraph U).mem_edgeSet.mpr hab)).1))
  have hBX := hB.local_host hTG hTseed hUG hUseed hhost hcap
  have hUX : ∀ e∈U,e∈(T⊔edgeGraph U).edgeSet := by
    intro e he
    rw [edgeSet_sup]
    exact Set.mem_union_right _ ((mem_edgeGraph U e).mpr ⟨he,G.not_isDiag_of_mem_edgeSet (hUG e he)⟩)
  have hpos := actual_threshold_gt_two heps hk
  obtain ⟨R,K,hRX,hK,hKT,hg,hweight⟩ := exists_heavy_girth_host hBX hT le_sup_left hTseed
    hUX hUseed (by intro e he;simp only [he,ite_true];exact (hhost e he).mono_left inter_subset_left)
    (fun e he => (hw e (edgeSet_mono hXG he)).le) hr (by linarith)
  have hRG : R≤G := hRX.trans hXG
  have hwR : ∀ e∈R.edgeSet,0<w e := fun e he => hw e (edgeSet_mono hRG he)
  have hKpos := tree_totalWeight_pos hK.2.1 hn w (fun e he => hwR e (edgeSet_mono hK.1 he))
  have hb := lightness_le_extremal hK hwR hg hpos hn (le_refl _)
  have hmul := (div_le_iff₀ hKpos).mp hb
  have hcoeff := extremalLightness_nonneg (Fintype.card V) hpos
  have hupper := hmul.trans (mul_le_mul_of_nonneg_left hKT hcoeff)
  have hsum := (div_le_iff₀ (show (0:ℝ)<4*(r:ℝ) by positivity)).mp (hweight.trans hupper)
  nlinarith
end LightEFTSpanners
