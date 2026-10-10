import LightEFTSpanners.ForestComponentPacking
import LightEFTSpanners.SeededSubtreePacking
import LightEFTSpanners.MissingEdgeConnectivity

namespace LightEFTSpanners
open SimpleGraph Finset LightSpanners HostCounting
variable {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
attribute [local instance] Classical.propDecidable

/-- A supplied forest family satisfying the source's actual edge-connectivity
requirements is enough. Native missing-edge connectivity is proved from the
true optimum seed; each forest is split into its genuine component trees. The
existence of these forests remains the separate packing theorem obligation. -/
theorem seeded_output_from_connectivity_forests {G Q : SimpleGraph V} {w : Sym2 V → ℝ}
    {eps : ℝ} {f k h q : ℕ} (hQ : IsMinimumFTPreserver G Q w q)
    (indices : Finset I) (F : I → SimpleGraph V)
    (hforest : ∀ i∈indices, (F i).IsAcyclic) (hFQ : ∀ i∈indices, F i≤Q)
    (hnumber : q+1 ≤ indices.card) (hbudget : 2*f+h ≤ q+1)
    (hconn : ∀ i∈indices, ∀ a b, Q.IsEdgeReachable (q+1) a b → (F i).Reachable a b)
    (hcong : ∀ e∈Q.edgeFinset, (hosts indices (fun i => (F i).edgeFinset) e).card ≤ 2)
    (hw0 : ∀ e, 0≤w e) (hw : ∀ e∈G.edgeSet, 0<w e)
    (hf : 0<f) (hk : 0<k) (heps : 0<eps) (hh : 0<h) :
    IsEFTSpanner G (output G Q w ((1+eps)*(2*k-1)) f) w ((1+eps)*(2*k-1)) f ∧
    competitiveLightness (output G Q w ((1+eps)*(2*k-1)) f) Q w ≤
      1+8*(f:ℝ)*(8+2048/eps*(Fintype.card V:ℝ)^((k:ℝ)⁻¹))/h := by
  have hQG : Q≤G := hQ.1.1
  have hkR : (1:ℝ)≤k := by exact_mod_cast hk
  have ht : (1:ℝ)≤(1+eps)*(2*k-1) := by
    have hp := mul_nonneg heps.le (sub_nonneg.mpr hkR)
    nlinarith
  have hsp := output_isEFTSpanner G Q hQG w ((1+eps)*(2*k-1)) f ht hw0
  refine ⟨hsp,?_⟩
  by_cases hz : totalWeight Q w=0
  · simp only [competitiveLightness,hz,div_zero]
    positivity
  · have hQnn : 0≤totalWeight Q w := by
      unfold totalWeight
      exact sum_nonneg (fun e _ => hw0 e)
    have hQpos : 0<totalWeight Q w := lt_of_le_of_ne hQnn (Ne.symm hz)
    obtain ⟨B,hB⟩ := output_has_blocking G Q hQG w ((1+eps)*(2*k-1)) f (by linarith)
    apply supplied_forest_packing_lightness (seed_le_output G Q w _ f) hQpos hB
      indices F hforest hFQ
    · intro a b hab habQ
      have hr := hQ.1.missing_edge_edgeReachable (hsp.1 hab) habQ
      have heq : indices.filter (fun i => (F i).Reachable a b)=indices := by
        apply filter_eq_self.mpr
        intro i hi
        exact hconn i hi a b hr
      rw [heq]
      exact hbudget.trans hnumber
    · exact hcong
    · exact fun e he => hw e (edgeSet_mono hsp.1 he)
    · exact hf
    · exact hk
    · exact heps
    · exact hh
end LightEFTSpanners
