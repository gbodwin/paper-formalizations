import LightEFTSpanners.ForestComponentPacking
import LightEFTSpanners.SubtreeHeavyLight

namespace LightEFTSpanners
open SimpleGraph Finset LightSpanners HostCounting
variable {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
attribute [local instance] Classical.propDecidable

/-- A supplied packing of actual forests with sufficient endpoint connectivity
reduces constructively to the heterogeneous-tree sampling theorem. Existence
of the forest packing is still an explicit structural premise. -/
theorem forest_packing_heavy_light_bound {G Q : SimpleGraph V} {w : Sym2 V → ℝ}
    {eps : ℝ} {f k r : ℕ} {B : Sym2 V → Finset (Sym2 V)}
    (hQG : Q ≤ G) (hQpos : 0 < totalWeight Q w)
    (hB : BlockingData G Q.edgeFinset w ((1+eps)*(2*k-1)) f B)
    (indices : Finset I) (F : I → SimpleGraph V)
    (hforest : ∀ i∈indices, (F i).IsAcyclic) (hFQ : ∀ i∈indices, F i≤Q)
    (hcount : ∀ a b, G.Adj a b → ¬Q.Adj a b →
      2*f+1 ≤ (indices.filter (fun i => (F i).Reachable a b)).card)
    (hcong : ∀ e∈Q.edgeFinset, (hosts indices (fun i => (F i).edgeFinset) e).card ≤ 2)
    (hw : ∀ e∈G.edgeSet, 0<w e) (hf : 0<f) (hk : 0<k) (heps : 0<eps) (hr : 0<r) (hrf : r≤f) (hfr : f≤r*(2*r+1)) :
    totalWeight G w / totalWeight Q w ≤
      1+16*(r:ℝ)*(8+2048/eps*(Fintype.card V:ℝ)^((k:ℝ)⁻¹)) := by
  classical
  let A : ForestComponentIndex F → Type _ := fun p => p.2
  let j : ∀ p, A p ↪ V := fun p => componentEmbedding (F p.1) p.2
  let T : ∀ p, SimpleGraph (A p) := fun p => p.2.toSimpleGraph
  apply subtree_heavy_light_bound hQG hQpos hB (forestComponentIndices indices F) j T
  · rintro ⟨i,c⟩ hi
    have hi' : i∈indices := by
      simpa only [forestComponentIndices,mem_sigma,mem_univ,and_true] using hi
    exact component_isTree (hforest i hi') c
  · rintro ⟨i,c⟩ hi
    have hi' : i∈indices := by
      simpa only [forestComponentIndices,mem_sigma,mem_univ,and_true] using hi
    exact (component_tree_le (F i) c).trans (hFQ i hi')
  · intro e he
    obtain ⟨a,b⟩ := e
    have ha : G.Adj a b := mem_edgeFinset.mp (mem_sdiff.mp he).1
    have hb : ¬Q.Adj a b := fun h => (mem_sdiff.mp he).2 (mem_edgeFinset.mpr h)
    exact (hcount a b ha hb).trans (forest_component_endpoint_count indices F a b)
  · intro e he
    exact (forest_component_congestion indices F e).trans (hcong e he)
  · exact hw
  · exact hf
  · exact hk
  · exact heps
  · exact hr
  · exact hrf
  · exact hfr
end LightEFTSpanners
