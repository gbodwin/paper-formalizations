import MinorFreeSpanners.InducedStarFamily
import MinorFreeSpanners.SeededBipartiteTrim

/-! Construct the regularized selected host while retaining every chosen
forest edge and every actual star branch. Global Unmated is not transported. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*}

/-- A graph between the chosen forest and the original host keeps the
literal induced-star packing. -/
theorem IsStarPacking.between_forest {G H : SimpleGraph V} {A C : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A C ell L)
    (hFH : starForestGraph C L ≤ H) (hHG : H ≤ G) : IsStarPacking H A C ell L := by
  refine ⟨h.1,h.2.1,?_,?_,h.2.2.2.2.1,h.2.2.2.2.2⟩
  · intro b x hx
    have hb : b ∈ C := by
      by_contra hn
      simp only [h.1 b hn,Finset.notMem_empty] at hx
    exact hFH ⟨(h.2.2.1 b x hx).ne,b,hb,Or.inl ⟨rfl,hx⟩⟩
  · intro b x hx y hy hxy he
    exact h.2.2.2.1 b x hx y hy hxy (hHG he)

/-- The selected induced graph is internally trimmed to exact integer left
degree m. Its forest, full coverage, size ratio and original mate threshold
are retained. No hereditary Unmated assertion is made. -/
theorem IsStarPacking.regularize_selected_host [Fintype V]
    {G : SimpleGraph V} {A B C : Finset V} {ell : ℕ} {L : V → Finset V}
    (h : IsStarPacking G A C ell L)
    (hG : G.IsBipartiteWith (A:Set V) (B:Set V)) (hCB : C ⊆ B)
    (hf : ∀ b ∈ C, (L b).card=ell) (q d eps : ℝ)
    (hfree : ∀ b ∈ C, MateFreeOn G q (insert b (L b:Set V)))
    (hdegree : ∀ x ∈ A, d ≤ (G.degree x:ℝ))
    (hboundary : ∀ x ∈ C.biUnion L,
      (((B \ C).filter fun y => G.Adj x y).card:ℝ) ≤ eps*d)
    (m : ℕ) (hm : 1 ≤ m) (hm' : (m:ℝ) ≤ (1-eps)*d) :
    ∃ H : SimpleGraph (SelectedStarVertex C L),
      starForestGraph (selectedStarCenters C L) (selectedStarAssignment C L) ≤ H ∧
      H ≤ G.induce ((C ∪ C.biUnion L:Finset V):Set V) ∧
      H.IsBipartiteWith (selectedStarLeaves C L:Set (SelectedStarVertex C L))
        (selectedStarCenters C L:Set (SelectedStarVertex C L)) ∧
      (∀ a ∈ selectedStarLeaves C L, H.degree a=m) ∧
      H.edgeFinset.card=m*(selectedStarLeaves C L).card ∧
      IsStarPacking H (selectedStarLeaves C L) (selectedStarCenters C L) ell
        (selectedStarAssignment C L) ∧
      (∀ b ∈ selectedStarCenters C L, (selectedStarAssignment C L b).card=ell) ∧
      (∀ b ∈ selectedStarCenters C L, MateFreeOn H q
        (insert b (selectedStarAssignment C L b:Set (SelectedStarVertex C L)))) ∧
      (selectedStarCenters C L).biUnion
        (fun b => insert b (selectedStarAssignment C L b))=Finset.univ ∧
      (selectedStarLeaves C L).card=ell*(selectedStarCenters C L).card := by
  classical
  have hp := h.induce_selected
  have hbip := h.selected_host_bipartite hG hCB
  have hAC := h.selected_domains_disjoint
    ((Finset.disjoint_coe.mp hG.disjoint).mono_right hCB)
  have hlow : ∀ a ∈ selectedStarLeaves C L,
      m ≤ (G.induce ((C ∪ C.biUnion L:Finset V):Set V)).degree a := by
    intro a ha
    have ha' : a.val ∈ C.biUnion L := Finset.mem_subtype.mp ha
    have hd' := h.selected_leaf_degree_ge hG d eps hdegree hboundary ha'
    have hmr := hm'.trans hd'
    exact_mod_cast hmr
  obtain ⟨H,hFH,hHG,hH,hreg,hcard⟩ := hp.exists_regular_supergraph_of_forest
    _ _ _ _ ell m _ hAC hbip hm hlow
  refine ⟨H,hFH,hHG,hH,hreg,hcard,hp.between_forest hFH hHG,
    h.induce_selected_full hf,?_,selected_star_family_covers C L,h.selected_size_ratio hf⟩
  intro b hb
  exact (h.selected_host_mateFree q hfree b hb).mono hHG

end MinorFreeSpanners
