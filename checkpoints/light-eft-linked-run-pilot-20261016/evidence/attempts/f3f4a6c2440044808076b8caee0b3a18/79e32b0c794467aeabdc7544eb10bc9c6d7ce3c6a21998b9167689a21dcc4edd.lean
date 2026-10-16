import LightEFTSpanners.ForestComponents
import LightEFTSpanners.SubtreeAssignments

namespace LightEFTSpanners
open SimpleGraph Finset LightSpanners HostCounting
variable {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
attribute [local instance] Classical.propDecidable

abbrev ForestComponentIndex (F : I → SimpleGraph V) := Σ i, (F i).ConnectedComponent

/-- Take every actual connected component of every supplied forest index. -/
noncomputable def forestComponentIndices (indices : Finset I) (F : I → SimpleGraph V) :
    Finset (ForestComponentIndex F) := indices.sigma (fun _ => univ)

omit [DecidableEq I] in
/-- Splitting forests into component trees cannot increase actual edge congestion. -/
theorem forest_component_congestion (indices : Finset I) (F : I → SimpleGraph V) (e : Sym2 V) :
    (hosts (forestComponentIndices indices F)
      (fun p => (p.2.toSimpleGraph.map (componentEmbedding (F p.1) p.2)).edgeFinset) e).card ≤
        (hosts indices (fun i => (F i).edgeFinset) e).card := by
  apply card_le_card_of_injOn Sigma.fst
  · rintro ⟨i,c⟩ hp
    obtain ⟨hp,he⟩ := mem_filter.mp hp
    have hi : i∈indices := by
      simpa only [forestComponentIndices,mem_sigma,mem_univ,and_true] using hp
    have he' : e∈(c.toSimpleGraph.map (componentEmbedding (F i) c)).edgeSet := by
      simpa only [mem_edgeFinset] using he
    exact mem_filter.mpr ⟨hi,mem_edgeFinset.mpr
      (edgeSet_mono (component_tree_le (F i) c) he')⟩
  · rintro ⟨i,c⟩ hp ⟨i',d⟩ hq hij
    change i=i' at hij
    subst i'
    have hc : e∈(c.toSimpleGraph.map (componentEmbedding (F i) c)).edgeSet := by
      simpa only [mem_edgeFinset] using (mem_filter.mp hp).2
    have hd : e∈(d.toSimpleGraph.map (componentEmbedding (F i) d)).edgeSet := by
      simpa only [mem_edgeFinset] using (mem_filter.mp hq).2
    have hcd := component_edge_unique (F i) hc hd
    cases hcd
    rfl

omit [DecidableEq I] in
/-- Each supplied forest connecting the actual endpoints contributes its
canonical component tree; distinct forest indices stay distinct. -/
theorem forest_component_endpoint_count (indices : Finset I) (F : I → SimpleGraph V) (a b : V) :
    (indices.filter (fun i => (F i).Reachable a b)).card ≤
      ((forestComponentIndices indices F).filter (fun p =>
        ∃ d, (componentEmbedding (F p.1) p.2).sym2Map d=s(a,b))).card := by
  apply card_le_card_of_injOn (fun i => ⟨i,(F i).connectedComponentMk a⟩)
  · intro i hi
    obtain ⟨hi,hreach⟩ := mem_filter.mp hi
    exact mem_filter.mpr ⟨by simp only [forestComponentIndices,mem_sigma,mem_univ,and_true,hi],
      reachable_component_pair hreach⟩
  · intro i _ j _ hij
    exact congrArg Sigma.fst hij

/-- A supplied packing of actual forests with sufficient endpoint connectivity
reduces constructively to the heterogeneous-tree sampling theorem. Existence
of the forest packing is still an explicit structural premise. -/
theorem supplied_forest_packing_lightness {G Q : SimpleGraph V} {w : Sym2 V → ℝ}
    {eps : ℝ} {f k h : ℕ} {B : Sym2 V → Finset (Sym2 V)}
    (hQG : Q ≤ G) (hQpos : 0 < totalWeight Q w)
    (hB : BlockingData G Q.edgeFinset w ((1+eps)*(2*k-1)) f B)
    (indices : Finset I) (F : I → SimpleGraph V)
    (hforest : ∀ i∈indices, (F i).IsAcyclic) (hFQ : ∀ i∈indices, F i≤Q)
    (hcount : ∀ a b, G.Adj a b → ¬Q.Adj a b →
      2*f+h ≤ (indices.filter (fun i => (F i).Reachable a b)).card)
    (hcong : ∀ e∈Q.edgeFinset, (hosts indices (fun i => (F i).edgeFinset) e).card ≤ 2)
    (hw : ∀ e∈G.edgeSet, 0<w e) (hf : 0<f) (hk : 0<k) (heps : 0<eps) (hh : 0<h) :
    totalWeight G w / totalWeight Q w ≤
      1+8*(f:ℝ)*(8+2048/eps*(Fintype.card V:ℝ)^((k:ℝ)⁻¹))/h := by
  classical
  let A : ForestComponentIndex F → Type _ := fun p => p.2
  let j : ∀ p, A p ↪ V := fun p => componentEmbedding (F p.1) p.2
  let T : ∀ p, SimpleGraph (A p) := fun p => p.2.toSimpleGraph
  apply subtree_packing_lightness hQG hQpos hB (forestComponentIndices indices F) j T
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
  · exact hh
end LightEFTSpanners
