import LightEFTSpanners.ExtremalForestHosts

namespace LightEFTSpanners
open SimpleGraph Finset LightSpanners HostCounting
variable {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
variable {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]
attribute [local instance] Classical.propDecidable

/-- Multiple actual host votes cancel the global fault factor while retaining
all seed weight. The coefficient is the real graph supremum. -/
theorem subtree_extremal_vote_bound {G Q : SimpleGraph V} {w : Sym2 V → ℝ}
    {eps : ℝ} {f k h : ℕ} {B : Sym2 V → Finset (Sym2 V)}
    (hQG : Q≤G) (hQpos : 0<totalWeight Q w)
    (hB : BlockingData G Q.edgeFinset w ((1+eps)*(2*k-1)) f B)
    (indices : Finset I) (j : ∀ i,A i ↪ V) (T : ∀ i,SimpleGraph (A i))
    (htrees : ∀ i∈indices,(T i).IsTree) (htreeQ : ∀ i∈indices,(T i).map (j i)≤Q)
    (hcount : ∀ e∈G.edgeFinset\Q.edgeFinset,
      2*f+h≤(indices.filter (fun i => ∃ d,(j i).sym2Map d=e)).card)
    (hcong : ∀ e∈Q.edgeFinset,(hosts indices (fun i => ((T i).map (j i)).edgeFinset) e).card≤2)
    (hw : ∀ e∈G.edgeSet,0<w e) (hf : 0<f) (hk : 0<k) (heps : 0<eps) (hh : 0<h) :
    totalWeight G w / totalWeight Q w ≤
      1+8*(f:ℝ)*extremalLightness (Fintype.card V) ((1+eps)*(2*k-1)+1)/h := by
  have hc := candidate_extremal_packing_bound (r:=f) (b:=f) hQG hB
    (G.edgeFinset\Q.edgeFinset) (Subset.refl _) indices j T htrees htreeQ hcount
    (fun e _ => (card_le_card inter_subset_left).trans (hB.capped e))
    (fun e _ => (card_le_card sdiff_subset).trans (hB.capped e)) hcong hw hf hk heps
  have hhR : (0:ℝ)<h := by exact_mod_cast hh
  have hadd : (∑ e∈G.edgeFinset\Q.edgeFinset,w e) ≤
      (8*(f:ℝ)*extremalLightness (Fintype.card V) ((1+eps)*(2*k-1)+1)*totalWeight Q w)/(h:ℝ) :=
    (le_div_iff₀ hhR).mpr (by nlinarith [hc])
  have hweight : totalWeight G w=totalWeight Q w+∑ e∈G.edgeFinset\Q.edgeFinset,w e := by
    unfold totalWeight
    have hs := sum_sdiff (f:=w) (edgeFinset_mono hQG)
    linarith
  apply (div_le_iff₀ hQpos).mpr
  rw [hweight]
  calc
    _ ≤ totalWeight Q w+(8*(f:ℝ)*extremalLightness (Fintype.card V) ((1+eps)*(2*k-1)+1)*totalWeight Q w)/(h:ℝ) := add_le_add le_rfl hadd
    _ = _ := by ring

/-- Genuine connected components of supplied forests provide the varying
vertex-domain hosts needed for the exact extremal multiple-vote estimate. -/
theorem forest_extremal_vote_bound {G Q : SimpleGraph V} {w : Sym2 V → ℝ}
    {eps : ℝ} {f k h : ℕ} {B : Sym2 V → Finset (Sym2 V)}
    (hQG : Q≤G) (hQpos : 0<totalWeight Q w)
    (hB : BlockingData G Q.edgeFinset w ((1+eps)*(2*k-1)) f B)
    (indices : Finset I) (F : I → SimpleGraph V)
    (hforest : ∀ i∈indices,(F i).IsAcyclic) (hFQ : ∀ i∈indices,F i≤Q)
    (hcount : ∀ a b,G.Adj a b → ¬Q.Adj a b →
      2*f+h≤(indices.filter (fun i => (F i).Reachable a b)).card)
    (hcong : ∀ e∈Q.edgeFinset,(hosts indices (fun i => (F i).edgeFinset) e).card≤2)
    (hw : ∀ e∈G.edgeSet,0<w e) (hf : 0<f) (hk : 0<k) (heps : 0<eps) (hh : 0<h) :
    totalWeight G w / totalWeight Q w ≤
      1+8*(f:ℝ)*extremalLightness (Fintype.card V) ((1+eps)*(2*k-1)+1)/h := by
  classical
  let A : ForestComponentIndex F → Type _ := fun p => p.2
  let j : ∀ p,A p ↪ V := fun p => componentEmbedding (F p.1) p.2
  let T : ∀ p,SimpleGraph (A p) := fun p => p.2.toSimpleGraph
  apply subtree_extremal_vote_bound hQG hQpos hB (forestComponentIndices indices F) j T
  · rintro ⟨i,c⟩ hi
    have hi' : i∈indices := by simpa only [forestComponentIndices,mem_sigma,mem_univ,and_true] using hi
    exact component_isTree (hforest i hi') c
  · rintro ⟨i,c⟩ hi
    have hi' : i∈indices := by simpa only [forestComponentIndices,mem_sigma,mem_univ,and_true] using hi
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
