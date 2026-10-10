import MinorFreeSpanners.EdgeContraction

/-! Exact finite edge count for the genuine simple-graph edge contraction. -/
namespace MinorFreeSpanners
open SimpleGraph
variable {V : Type*} (G : SimpleGraph V) (u v : V)

instance contractEdgeDecidableAdj [DecidableEq V] [DecidableRel G.Adj] :
    DecidableRel (contractEdge G u v).Adj := by
  intro a b
  change Decidable (a ≠ b ∧ (G.Adj a.val b.val ∨
    (a.val = u ∧ G.Adj v b.val) ∨ (b.val = u ∧ G.Adj a.val v)))
  infer_instance

/-- The merged vertex's neighbors are exactly the union of the two old
neighborhoods, with both contracted endpoints removed. -/
theorem contractEdge_map_neighborFinset [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (huv : G.Adj u v) :
    ((contractEdge G u v).neighborFinset ⟨u, huv.ne⟩).map
      (Function.Embedding.subtype fun x => x ≠ v) =
        ((G.neighborFinset u ∪ G.neighborFinset v).erase u).erase v := by
  classical
  ext x
  simp only [Finset.mem_map, Finset.mem_erase, Finset.mem_union, mem_neighborFinset]
  constructor
  · rintro ⟨y, hy, rfl⟩
    change ⟨u, huv.ne⟩ ≠ y ∧ _ at hy
    refine ⟨y.property, ?_, ?_⟩
    · intro h
      exact hy.1 (Subtype.ext h.symm)
    · rcases hy.2 with h | ⟨_, h⟩ | ⟨h, _⟩
      · exact Or.inl h
      · exact Or.inr h
      · exact False.elim (hy.1 (Subtype.ext h.symm))
  · rintro ⟨hxv, hxu, hx⟩
    refine ⟨⟨x, hxv⟩, ?_, rfl⟩
    change (⟨u, huv.ne⟩ : {x : V // x ≠ v}) ≠ ⟨x, hxv⟩ ∧ _
    refine ⟨fun h => hxu (congrArg Subtype.val h).symm, ?_⟩
    rcases hx with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨rfl, h⟩)

/-- Contracting an edge removes that edge and exactly one duplicate edge
for every common neighbor of its endpoints. -/
theorem contractEdge_edge_count [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (huv : G.Adj u v) :
    (contractEdge G u v).edgeFinset.card + 1 +
      Fintype.card (G.commonNeighbors u v) = G.edgeFinset.card := by
  classical
  let a : {x : V // x ≠ v} := ⟨u, huv.ne⟩
  let H : SimpleGraph {x : V // x ≠ v} := G.comap Subtype.val
  let K := contractEdge G u v
  have hdel : K.deleteIncidenceSet a = H.deleteIncidenceSet a := by
    ext b c
    simp only [deleteIncidenceSet_adj]
    change (b ≠ c ∧ (G.Adj b.val c.val ∨
      (b.val = u ∧ G.Adj v c.val) ∨ (c.val = u ∧ G.Adj b.val v))) ∧
      b ≠ a ∧ c ≠ a ↔ G.Adj b.val c.val ∧ b ≠ a ∧ c ≠ a
    constructor
    · rintro ⟨⟨_, h | ⟨h, _⟩ | ⟨h, _⟩⟩, hb, hc⟩
      · exact ⟨h, hb, hc⟩
      · exact False.elim (hb (Subtype.ext h))
      · exact False.elim (hc (Subtype.ext h))
    · rintro ⟨h, hb, hc⟩
      exact ⟨⟨fun hbc => h.ne (congrArg Subtype.val hbc), Or.inl h⟩, hb, hc⟩
  have hHmap : (H.neighborFinset a).map
      (Function.Embedding.subtype fun x => x ≠ v) = (G.neighborFinset u).erase v := by
    ext x
    simp only [Finset.mem_map, Finset.mem_erase, mem_neighborFinset]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · rintro ⟨hxv, hx⟩
      exact ⟨⟨x, hxv⟩, hx, rfl⟩
  have hHdegree : H.degree a + 1 = G.degree u := by
    have h := congrArg Finset.card hHmap
    have he := Finset.card_erase_add_one (s := G.neighborFinset u) (a := v)
      (show v ∈ G.neighborFinset u by simpa using huv)
    simp only [Finset.card_map, card_neighborFinset_eq_degree] at h he
    omega
  have hKdegree : K.degree a + 2 + Fintype.card (G.commonNeighbors u v) =
      G.degree u + G.degree v := by
    have hmap := congrArg Finset.card (contractEdge_map_neighborFinset G u v huv)
    have hu : u ∈ G.neighborFinset u ∪ G.neighborFinset v := by
      simp [huv.symm]
    have hv : v ∈ (G.neighborFinset u ∪ G.neighborFinset v).erase u := by
      simp [huv, huv.ne.symm]
    have heu := Finset.card_erase_add_one hu
    have hev := Finset.card_erase_add_one hv
    have hunion := Finset.card_union_add_card_inter (G.neighborFinset u) (G.neighborFinset v)
    have hinter : G.neighborFinset u ∩ G.neighborFinset v =
        (G.commonNeighbors u v).toFinset := by
      ext x
      simp [mem_commonNeighbors]
    rw [hinter, Set.toFinset_card] at hunion
    simp only [Finset.card_map, card_neighborFinset_eq_degree] at hmap hunion
    change K.degree a = _ at hmap
    omega
  have hGdel := G.card_edgeFinset_deleteIncidenceSet v
  have hHcard : H.edgeFinset.card = G.edgeFinset.card - G.degree v := by
    exact (G.card_edgeFinset_induce_compl_singleton v).trans hGdel
  have hKdel := K.card_edgeFinset_deleteIncidenceSet a
  have hHdel := H.card_edgeFinset_deleteIncidenceSet a
  have hdelcard : (K.deleteIncidenceSet a).edgeFinset.card =
      (H.deleteIncidenceSet a).edgeFinset.card := by
    exact congrArg Finset.card (SimpleGraph.edgeFinset_inj.mpr hdel)
  have hGbound := G.degree_le_card_edgeFinset v
  have hHbound := H.degree_le_card_edgeFinset a
  have hKbound := K.degree_le_card_edgeFinset a
  change K.edgeFinset.card + 1 + Fintype.card (G.commonNeighbors u v) = G.edgeFinset.card
  omega

/-- Subtractive form of the exact edge count. -/
theorem contractEdge_edge_count_sub [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (huv : G.Adj u v) :
    (contractEdge G u v).edgeFinset.card =
      G.edgeFinset.card - 1 - Fintype.card (G.commonNeighbors u v) := by
  have h := contractEdge_edge_count G u v huv
  omega

end MinorFreeSpanners
