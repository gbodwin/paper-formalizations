import MinorFreeSpanners.GreedyNeighborhoodCover

/-! Actual finite neighborhood packing for the high-degree clustering phase.
Every eligible unmarked vertex has an edge into the constructed marked set. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

noncomputable def closedNeighborhood {V : Type*} [Fintype V]
    (G : SimpleGraph V) (v : V) : Finset V := by
  classical
  exact insert v (G.neighborFinset v)

@[simp] theorem mem_closedNeighborhood {V : Type*} [Fintype V]
    (G : SimpleGraph V) (v x : V) : x ∈ closedNeighborhood G v ↔ x=v ∨ G.Adj v x := by
  classical
  simp [closedNeighborhood]

theorem exists_disjoint_neighborhood_packing {V : Type*} [Fintype V]
    (G : SimpleGraph V) (S : Finset V) :
    ∃ C : Finset V, C ⊆ S ∧
      (∀ c∈C, ∀ c'∈C, c ≠ c' → Disjoint (closedNeighborhood G c) (closedNeighborhood G c')) ∧
      ∀ v∈S, v ∉ C.biUnion (closedNeighborhood G) →
        ∃ u∈C.biUnion (closedNeighborhood G), G.Adj v u := by
  classical
  let good (C : Finset V) : Prop := C ⊆ S ∧
    (∀ c∈C, ∀ c'∈C, c ≠ c' → Disjoint (closedNeighborhood G c) (closedNeighborhood G c'))
  let candidates := (Finset.univ : Finset (Finset V)).filter good
  have h0 : (∅:Finset V) ∈ candidates := by simp [candidates,good]
  obtain ⟨C,hC,hmax⟩ := Finset.exists_max_image candidates Finset.card ⟨_,h0⟩
  have hgood := (Finset.mem_filter.mp hC).2
  refine ⟨C,hgood.1,hgood.2,?_⟩
  intro v hv hnot
  by_contra hn
  push Not at hn
  have hvc : v∉C := by
    intro hc
    apply hnot
    exact Finset.mem_biUnion.mpr ⟨v,hc,by simp⟩
  have hdisj (c : V) (hc : c∈C) : Disjoint (closedNeighborhood G v) (closedNeighborhood G c) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hxW : x∈C.biUnion (closedNeighborhood G) := Finset.mem_biUnion.mpr ⟨c,hc,hy⟩
    rcases (mem_closedNeighborhood G v x).mp hx with rfl | hAdj
    · exact hnot hxW
    · exact hn x hxW hAdj
  have hpair : ∀ c∈insert v C, ∀ c'∈insert v C, c ≠ c' →
      Disjoint (closedNeighborhood G c) (closedNeighborhood G c') := by
    intro x hx y hy hxy
    rcases Finset.mem_insert.mp hx with hxe | hxC
    · subst x
      rcases Finset.mem_insert.mp hy with hye | hyC
      · exact (hxy hye.symm).elim
      · exact hdisj y hyC
    · rcases Finset.mem_insert.mp hy with hye | hyC
      · subst y
        exact (hdisj x hxC).symm
      · exact hgood.2 x hxC y hyC hxy
  have hins : insert v C ∈ candidates := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_,hpair⟩
    exact Finset.insert_subset hv hgood.1
  have hh := hmax (insert v C) hins
  rw [Finset.card_insert_of_notMem hvc] at hh
  omega

end MinorFreeSpanners
