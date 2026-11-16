import LightEFTSpanners.CorrectedCloudConnectivity
import LightEFTSpanners.CorrectedCloudSpannerWeight
import LightEFTSpanners.CorrectedCloudParameters
import LightEFTSpanners.CorrectedExtremalBoundary
import LightEFTSpanners.PreserverWeightPositivity

/-! The corrected Theorem 34, against actual minimum-weight fault connectivity
preservers. The construction and its all-fault spanner forcing are proved in
the imported cloud modules; no denominator or retention oracle is assumed. -/
namespace LightEFTSpanners.CorrectedCloud
open SimpleGraph Finset LightSpanners
attribute [local instance] Classical.propDecidable

/-- The literal cloud construction transfers the lightness of every positive
high-weighted-girth core to every actual fault-tolerant spanner. -/
theorem cloud_competitive_lower {m p f q : ℕ} {G T : SimpleGraph (Fin m)}
    (w : Sym2 (Fin m) → ℝ) (t : ℝ)
    (hT : IsMinimumSpanningTree G T w) (hw : ∀e∈G.edgeSet,0<w e)
    (hm : 2≤m) (hp : 2≤p) (hfp : f<p) (hqp : q≤p)
    (hg : WeightedGirthAbove G w (t+1))
    {H Q : SimpleGraph (Fin m × Fin p)}
    (hsp : IsEFTSpanner (graph G p) H (cloudWeight T w p) t f)
    (hQ : IsMinimumFTPreserver (graph G p) Q (cloudWeight T w p) q) :
    (((f:ℝ)+1)/(2*(p:ℝ)+1))*lightness G T w ≤
      competitiveLightness H Q (cloudWeight T w p) := by
  have hL : 0<totalWeight T w := tree_totalWeight_pos hT.2.1 (by simpa using hm) w
    (fun e he => hw e (edgeSet_mono hT.1 he))
  have hpos := cloudWeight_positive hT hw hm (by omega : 0<p)
  have hcert : IsFTConnectivityPreserver (graph G p) (certificate T p) q :=
    (certificate_isFTPreserver hT.1 hT.2.1.connected hm hp).fault_mono hqp
  have hden := (hQ.2 (certificate T p) hcert).trans
    (cloud_certificate_weight_le T w (by omega) (by omega)
      (fun e he => (hw e (edgeSet_mono hT.1 he)).le))
  have hnum := cloud_spanner_weight_lower w t hT hw hm hfp hg hsp
  let : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
  let u : Fin m := ⟨0,by omega⟩
  let i : Fin p := ⟨0,by omega⟩
  obtain ⟨v,huv⟩ := hT.2.1.connected.preconnected.exists_adj_of_nontrivial u
  have hQpos : 0<totalWeight Q (cloudWeight T w p) :=
    preserver_weight_pos_of_adj hQ.1 hpos
      (show (graph G p).Adj (u,i) (v,i) from Or.inr (hT.1 huv))
  have hGnn : 0≤totalWeight G w := sum_nonneg (fun e he => (hw e (mem_edgeFinset.mp he)).le)
  have hcoef : 0≤(((f:ℝ)+1)/(2*(p:ℝ)+1))*lightness G T w := by
    unfold lightness
    positivity
  unfold competitiveLightness
  apply (le_div_iff₀ hQpos).mpr
  calc
    _ ≤ ((((f:ℝ)+1)/(2*(p:ℝ)+1))*lightness G T w)*
        ((2*(p:ℝ)+1)*totalWeight T w) := mul_le_mul_of_nonneg_left hden hcoef
    _ = ((f:ℝ)+1)*totalWeight G w := by
      unfold lightness
      field_simp
    _ ≤ _ := hnum

/-- An exact-order family at arbitrary real stretch, retaining the full
extremal function. Both the input and its positive edge weights are produced. -/
theorem exists_cloud_extremal_lower {m p f q : ℕ} {t : ℝ}
    (hm : 2≤m) (hp : 2≤p) (hfp : f<p) (hqp : q≤p) (ht : 1≤t) :
    ∃ G : SimpleGraph (Fin m × Fin p), ∃ W : Sym2 (Fin m × Fin p) → ℝ,
      (∀e∈G.edgeSet,0<W e) ∧
      (∀H : SimpleGraph (Fin m × Fin p), IsEFTSpanner G H W t f →
        ∀Q : SimpleGraph (Fin m × Fin p), IsMinimumFTPreserver G Q W q →
          (((f:ℝ)+1)/(2*(p:ℝ)+1))*(extremalLightness m (t+1)/2) ≤
            competitiveLightness H Q W) := by
  obtain ⟨G,T,w,hT,hw,hg,hnear⟩ := corrected_exists_near_extremal hm (by linarith : 2≤t+1)
  refine ⟨graph G p,cloudWeight T w p,cloudWeight_positive hT hw hm (by omega),?_⟩
  intro H hsp Q hQ
  exact (mul_le_mul_of_nonneg_left hnear.le (by positivity)).trans
    (cloud_competitive_lower w t hT hw hm hp hfp hqp hg hsp hQ)

/-- With p=floor(cf), the exact-order cloud family has the paper's lower
bound, with the explicit constant 1/(4c). Natural order arguments are rounded
down in the extremal function. -/
theorem exists_cf_cloud_lower {m f : ℕ} {c t : ℝ}
    (hm : 2≤m) (hc : 2≤c) (hf : 1≤f) (ht : 1≤t) :
    ∃ G : SimpleGraph (Fin m × Fin (cloudSize c f)),
      ∃ W : Sym2 (Fin m × Fin (cloudSize c f)) → ℝ,
      (∀e∈G.edgeSet,0<W e) ∧
      (∀H : SimpleGraph (Fin m × Fin (cloudSize c f)), IsEFTSpanner G H W t f →
        ∀Q : SimpleGraph (Fin m × Fin (cloudSize c f)),
          IsMinimumFTPreserver G Q W (cloudSize c f) →
          extremalLightness ⌊((m*cloudSize c f : ℕ):ℝ)/(c*(f:ℝ))⌋₊ (t+1)/(4*c) ≤
            competitiveLightness H Q W) := by
  obtain ⟨G,W,hpos,hbound⟩ := exists_cloud_extremal_lower hm
    (two_le_cloudSize hc hf) (fault_lt_cloudSize hc hf) le_rfl ht
  refine ⟨G,W,hpos,?_⟩
  intro H hsp Q hQ
  have hg : 2≤t+1 := by linarith
  have hnonneg := corrected_extremalLightness_nonneg m hg
  have hmono := corrected_extremalLightness_mono (core_order_ge_scaled_order hc hf m) hg
  calc
    _ ≤ extremalLightness m (t+1)/(4*c) :=
      div_le_div_of_nonneg_right hmono (by positivity)
    _ = (1/(2*c))*(extremalLightness m (t+1)/2) := by ring
    _ ≤ (((f:ℝ)+1)/(2*(cloudSize c f : ℝ)+1))*(extremalLightness m (t+1)/2) :=
      mul_le_mul_of_nonneg_right (cloudSize_coefficient hc f) (by positivity)
    _ ≤ _ := hbound H hsp Q hQ

/-- Corrected Theorem 34 as an actual infinite family: for each order cutoff
there is a larger positive-weight input, and every f-EFT real-t-spanner has
competitive lightness at least lambda(floor(n/(cf)),t+1)/(4c), against every
genuine minimum floor(cf)-fault connectivity preserver. -/
theorem corrected_theorem34 {c t : ℝ} {f : ℕ}
    (hc : 2≤c) (hf : 1≤f) (ht : 1≤t) (N : ℕ) :
    ∃ m : ℕ, ∃ G : SimpleGraph (Fin m × Fin (cloudSize c f)),
      ∃ W : Sym2 (Fin m × Fin (cloudSize c f)) → ℝ,
      2≤m ∧ N<Fintype.card (Fin m × Fin (cloudSize c f)) ∧
      (∀e∈G.edgeSet,0<W e) ∧
      (∀H : SimpleGraph (Fin m × Fin (cloudSize c f)), IsEFTSpanner G H W t f →
        ∀Q : SimpleGraph (Fin m × Fin (cloudSize c f)),
          IsMinimumFTPreserver G Q W (cloudSize c f) →
          extremalLightness
            ⌊(Fintype.card (Fin m × Fin (cloudSize c f)) : ℝ)/(c*(f:ℝ))⌋₊ (t+1)/(4*c) ≤
              competitiveLightness H Q W) := by
  obtain ⟨G,W,hpos,hbound⟩ := exists_cf_cloud_lower (by omega : 2≤N+2) hc hf ht
  refine ⟨N+2,G,W,by omega,?_,hpos,?_⟩
  · simp only [Fintype.card_prod,Fintype.card_fin]
    have hp : 1≤cloudSize c f := by have h := two_le_cloudSize hc hf; omega
    have hmul := Nat.mul_le_mul_left (N+2) hp
    omega
  · simpa only [Fintype.card_prod,Fintype.card_fin] using hbound

end LightEFTSpanners.CorrectedCloud
