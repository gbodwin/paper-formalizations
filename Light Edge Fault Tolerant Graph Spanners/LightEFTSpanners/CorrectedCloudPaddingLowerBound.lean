import LightEFTSpanners.CorrectedCloudPaddingTransport
import Mathlib.Data.Fintype.EquivFin

/-! The corrected lower bound at each prescribed sufficiently large order.
Unused vertices are isolated; the actual EFT definitions preserve components,
and the padding transport proves that their presence changes no ratio. -/
namespace LightEFTSpanners.CorrectedCloud
open SimpleGraph Finset LightSpanners
attribute [local instance] Classical.propDecidable

theorem scaled_order_le_quotient {c : ℝ} (hc : 2≤c) {f : ℕ} (hf : 1≤f)
    (n : ℕ) : ⌊(n:ℝ)/(c*(f:ℝ))⌋₊≤n/cloudSize c f := by
  have hp : 0<cloudSize c f := by have h := two_le_cloudSize hc hf; omega
  have hcf : 0<c*(f:ℝ) := by positivity
  apply (Nat.le_div_iff_mul_le hp).mpr
  have hfloor : (⌊(n:ℝ)/(c*(f:ℝ))⌋₊ : ℝ)≤(n:ℝ)/(c*(f:ℝ)) :=
    Nat.floor_le (by positivity)
  have hscaled := (le_div_iff₀ hcf).mp hfloor
  have hproduct := mul_le_mul_of_nonneg_left (cloudSize_cast_le hc f)
    (Nat.cast_nonneg ⌊(n:ℝ)/(c*(f:ℝ))⌋₊ : (0:ℝ)≤⌊(n:ℝ)/(c*(f:ℝ))⌋₊)
  exact_mod_cast hproduct.trans hscaled

/-- Corrected Theorem 34 for every prescribed n≥2floor(cf), with the same
explicit constant 1/(4c) and arbitrary real stretch t≥1. -/
theorem corrected_theorem34_every_order {c t : ℝ} {f n : ℕ}
    (hc : 2≤c) (hf : 1≤f) (ht : 1≤t) (hn : 2*cloudSize c f≤n) :
    ∃ G : SimpleGraph (Fin n), ∃ W : Sym2 (Fin n) → ℝ,
      (∀e∈G.edgeSet,0<W e) ∧
      (∀H : SimpleGraph (Fin n), IsEFTSpanner G H W t f →
        ∀Q : SimpleGraph (Fin n), IsMinimumFTPreserver G Q W (cloudSize c f) →
          extremalLightness ⌊(n:ℝ)/(c*(f:ℝ))⌋₊ (t+1)/(4*c) ≤
            competitiveLightness H Q W) := by
  have hp := two_le_cloudSize hc hf
  have hppos : 0<cloudSize c f := by omega
  have hm : 2≤n/cloudSize c f := (Nat.le_div_iff_mul_le hppos).mpr hn
  obtain ⟨G,w,hw,hbound⟩ := exists_cloud_extremal_lower hm hp
    (fault_lt_cloudSize hc hf) le_rfl ht
  have hcard : Fintype.card (Fin (n/cloudSize c f) × Fin (cloudSize c f))≤Fintype.card (Fin n) := by
    simpa only [Fintype.card_prod,Fintype.card_fin] using Nat.div_mul_le_self n (cloudSize c f)
  obtain ⟨j⟩ : Nonempty ((Fin (n/cloudSize c f) × Fin (cloudSize c f)) ↪ Fin n) :=
    Function.Embedding.nonempty_of_card_le hcard
  let : Nonempty (Fin (n/cloudSize c f) × Fin (cloudSize c f)) :=
    ⟨(⟨0,by omega⟩,⟨0,hppos⟩)⟩
  let r : Fin n → Fin (n/cloudSize c f) × Fin (cloudSize c f) := Function.invFun j
  have hj : Function.LeftInverse r j := Function.leftInverse_invFun j.injective
  refine ⟨G.map j,Padding.weight r w,Padding.positive_map j r hj hw,?_⟩
  intro H hsp Q hQ
  rw [Padding.competitiveLightness_restrict j r hj hsp.1 hQ.1.1 w]
  have hsp₀ := Padding.eft_restrict j r hj hsp
  have hQ₀ := Padding.minimum_preserver_restrict j r hj hQ
  have hg : 2≤t+1 := by linarith
  have hnonneg := corrected_extremalLightness_nonneg (n/cloudSize c f) hg
  have hmono := corrected_extremalLightness_mono (scaled_order_le_quotient hc hf n) hg
  calc
    _ ≤ extremalLightness (n/cloudSize c f) (t+1)/(4*c) :=
      div_le_div_of_nonneg_right hmono (by positivity)
    _ = (1/(2*c))*(extremalLightness (n/cloudSize c f) (t+1)/2) := by ring
    _ ≤ (((f:ℝ)+1)/(2*(cloudSize c f : ℝ)+1))*
        (extremalLightness (n/cloudSize c f) (t+1)/2) :=
      mul_le_mul_of_nonneg_right (cloudSize_coefficient hc f) (by positivity)
    _ ≤ _ := hbound (H.comap j) hsp₀ (Q.comap j) hQ₀

end LightEFTSpanners.CorrectedCloud
