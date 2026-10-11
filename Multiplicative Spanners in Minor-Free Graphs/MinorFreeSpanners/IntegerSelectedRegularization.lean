import MinorFreeSpanners.SelectedStarRegularization

namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*}

/-- Integer boundary counts permit the exact natural degree m whenever
m+dA<=d. This retains the forest and avoids rounding a real degree bound down
unnecessarily. Global Unmated is still not transported. -/
theorem IsStarPacking.regularize_selected_host_integer [Fintype V]
    {G : SimpleGraph V} {A B C : Finset V} {ell : ℕ} {L : V → Finset V}
    (h : IsStarPacking G A C ell L)
    (hG : G.IsBipartiteWith (A:Set V) (B:Set V)) (hCB : C ⊆ B)
    (hf : ∀ b ∈ C, (L b).card=ell) (q : ℝ) (d dA : ℕ)
    (hfree : ∀ b ∈ C, MateFreeOn G q (insert b (L b:Set V)))
    (hdegree : ∀ x ∈ A, d ≤ G.degree x)
    (hboundary : ∀ x ∈ C.biUnion L,
      ((B \ C).filter fun y => G.Adj x y).card ≤ dA)
    (m : ℕ) (hm : 1 ≤ m) (hm' : m+dA ≤ d) :
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
    have he := h.selected_leaf_degree hG ha'
    have hd := hdegree a.val (h.covered_subset ha')
    have hb := hboundary a.val ha'
    have he' : (G.induce ((C ∪ C.biUnion L:Finset V):Set V)).degree a +
        ((B \ C).filter fun y => G.Adj a.val y).card=G.degree a.val := by
      simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at he ⊢
      convert he using 1
    omega
  obtain ⟨H,hFH,hHG,hH,hreg,hcard⟩ := hp.exists_regular_supergraph_of_forest
    _ _ _ _ ell m _ hAC hbip hm hlow
  refine ⟨H,hFH,hHG,hH,hreg,hcard,hp.between_forest hFH hHG,
    h.induce_selected_full hf,?_,selected_star_family_covers C L,h.selected_size_ratio hf⟩
  intro b hb
  exact (h.selected_host_mateFree q hfree b hb).mono hHG

end MinorFreeSpanners
