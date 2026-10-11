import MinorFreeSpanners.MateFreeStarContraction

/-! The actual induced host on the selected centers and leaves. Its leaf
degrees lose precisely the counted boundary edges, not an assumed fraction. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

/-- Every original leaf neighbor that remains in the selected induced host
is an actual selected center. -/
theorem IsStarPacking.selected_leaf_degree {G : SimpleGraph V}
    {A B C : Finset V} {ell : ℕ} {L : V → Finset V}
    (h : IsStarPacking G A C ell L)
    (hG : G.IsBipartiteWith (A:Set V) (B:Set V))
    {x : V} (hx : x ∈ C.biUnion L) :
    (G.induce ((C ∪ C.biUnion L : Finset V):Set V)).degree
      ⟨x,Finset.mem_union_right C hx⟩ +
      ((B \ C).filter fun y => G.Adj x y).card = G.degree x := by
  classical
  let S := C ∪ C.biUnion L
  have hxA := h.covered_subset hx
  have hN : ∀ y, G.Adj x y → y ∈ B := fun y he => hG.mem_of_mem_adj hxA he
  have hno : ∀ y ∈ C.biUnion L, ¬G.Adj x y := by
    intro y hy he
    exact hG.disjoint.le_bot ⟨h.covered_subset hy,hN y he⟩
  have hfilter : (G.neighborFinset x).filter (fun y => y ∈ C) =
      C.filter (fun y => G.Adj x y) := by
    ext y
    simp only [Finset.mem_filter,mem_neighborFinset]
    exact and_comm
  have hother : (G.neighborFinset x).filter (fun y => y ∉ C) =
      (B \ C).filter (fun y => G.Adj x y) := by
    ext y
    simp only [Finset.mem_filter,mem_neighborFinset,Finset.mem_sdiff]
    exact ⟨fun hy => ⟨⟨hN y hy.1,hy.2⟩,hy.1⟩,fun hy => ⟨hy.2,hy.1.2⟩⟩
  have hinter : G.neighborFinset x ∩ S = C.filter (fun y => G.Adj x y) := by
    ext y
    simp only [Finset.mem_inter,mem_neighborFinset,Finset.mem_filter,S,Finset.mem_union]
    constructor
    · rintro ⟨he,hc|hl⟩
      · exact ⟨hc,he⟩
      · exact (hno y hl he).elim
    · exact fun hy => ⟨hy.2,Or.inl hy.1⟩
  have hi := G.map_neighborFinset_induce (s:=(S:Set V))
    (⟨x,Finset.mem_union_right C hx⟩ : (S:Set V))
  have hic := congrArg Finset.card hi
  simp only [Finset.card_map,card_neighborFinset_eq_degree,Finset.coe_sort_coe,
    Finset.toFinset_coe,hinter] at hic
  have hs := Finset.card_filter_add_card_filter_not (s:=G.neighborFinset x)
    (fun y => y ∈ C)
  rw [hfilter,hother,card_neighborFinset_eq_degree] at hs
  simp only [S, ← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hic hs ⊢
  omega

/-- The selection boundary estimate gives the actual induced minimum
left degree, even though the selected centers need not cover B. -/
theorem IsStarPacking.selected_leaf_degree_ge {G : SimpleGraph V}
    {A B C : Finset V} {ell : ℕ} {L : V → Finset V}
    (h : IsStarPacking G A C ell L)
    (hG : G.IsBipartiteWith (A:Set V) (B:Set V))
    (d eps : ℝ) (hdegree : ∀ x ∈ A, d ≤ (G.degree x:ℝ))
    (hboundary : ∀ x ∈ C.biUnion L,
      (((B \ C).filter fun y => G.Adj x y).card:ℝ) ≤ eps*d)
    {x : V} (hx : x ∈ C.biUnion L) :
    (1-eps)*d ≤ ((G.induce ((C ∪ C.biUnion L : Finset V):Set V)).degree
      ⟨x,Finset.mem_union_right C hx⟩:ℝ) := by
  have he := h.selected_leaf_degree hG hx
  have heR := congrArg (fun n : ℕ => (n:ℝ)) he
  push_cast at heR
  have hd := hdegree x (h.covered_subset hx)
  have hb := hboundary x hx
  nlinarith

end MinorFreeSpanners
