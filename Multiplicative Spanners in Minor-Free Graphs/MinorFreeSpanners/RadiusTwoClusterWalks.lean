import MinorFreeSpanners.RadiusTwoClustering

namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

/-- The actual radius-two certificate gives a walk entirely inside its branch. -/
theorem radius_two_walk_to_center {V : Type*} [Fintype V]
    (G : SimpleGraph V) (c : V) (B : Finset V)
    (hcore : closedNeighborhood G c ⊆ B) {v : V} (hv : v∈B)
    (hnear : v∈closedNeighborhood G c ∨
      ∃ u∈closedNeighborhood G c, G.Adj v u) :
    ∃ p : G.Walk v c, (∀ x∈p.support, x∈B) ∧ p.length ≤ 2 := by
  classical
  have hc : c∈B := hcore (by simp)
  have hshort (u : V) (hu : u∈closedNeighborhood G c) :
      ∃ p : G.Walk u c, (∀ x∈p.support, x∈B) ∧ p.length ≤ 1 := by
    rcases (mem_closedNeighborhood G c u).mp hu with rfl | hadj
    · exact ⟨.nil,by simpa using hc,by simp⟩
    · refine ⟨.cons hadj.symm .nil,?_,by simp⟩
      simpa using And.intro (hcore hu) hc
  rcases hnear with hcorev | ⟨u,hu,hvu⟩
  · obtain ⟨p,hp,hl⟩ := hshort v hcorev
    exact ⟨p,hp,by omega⟩
  · obtain ⟨p,hp,hl⟩ := hshort u hu
    refine ⟨.cons hvu p,?_,by simpa using Nat.add_le_add_right hl 1⟩
    simpa using And.intro hv hp

/-- The complete high-degree clustering phase: every high-degree vertex is
covered, each branch keeps at least q+1 original vertices, and actual walks
inside each branch have length at most four. Uncovered vertices are low degree. -/
theorem exists_high_degree_clustering {V : Type*} [Fintype V]
    (G : SimpleGraph V) (q : ℕ) :
    ∃ C : Finset V, ∃ B : V → Finset V,
      (∀ c∈C, q ≤ G.degree c) ∧
      (∀ c∈C, closedNeighborhood G c ⊆ B c) ∧
      (∀ c∈C, q+1 ≤ (B c).card) ∧
      (∀ c∈C, ∀ c'∈C, c ≠ c' → Disjoint (B c) (B c')) ∧
      (∀ c∈C, ∀ x∈B c, ∀ y∈B c,
        ∃ p : G.Walk x y, (∀ z∈p.support, z∈B c) ∧ p.length ≤ 4) ∧
      (∀ v, v∉C.biUnion B → G.degree v < q) := by
  classical
  let S := (Finset.univ : Finset V).filter (fun v => q ≤ G.degree v)
  obtain ⟨C,B,hCS,hcore,hdis,hunion,hnear⟩ := exists_radius_two_clustering G S
  refine ⟨C,B,?_,hcore,?_,hdis,?_,?_⟩
  · intro c hc
    exact (Finset.mem_filter.mp (hCS hc)).2
  · intro c hc
    have hcard : (closedNeighborhood G c).card = G.degree c + 1 := by
      simp [closedNeighborhood]
    have hq := (Finset.mem_filter.mp (hCS hc)).2
    have hh := Finset.card_le_card (hcore c hc)
    omega
  · intro c hc x hx y hy
    obtain ⟨p,hp,hlp⟩ := radius_two_walk_to_center G c (B c) (hcore c hc) hx (hnear c hc x hx)
    obtain ⟨r,hr,hlr⟩ := radius_two_walk_to_center G c (B c) (hcore c hc) hy (hnear c hc y hy)
    refine ⟨p.append r.reverse,?_,?_⟩
    · intro z hz
      rcases (Walk.mem_support_append_iff p r.reverse).mp hz with hz | hz
      · exact hp z hz
      · exact hr z (by simpa using hz)
    · simp only [Walk.length_append,Walk.length_reverse]
      omega
  · intro v hv
    by_contra hn
    have hs : v∈S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩
    apply hv
    rw [hunion]
    exact Finset.mem_union_right _ hs

end MinorFreeSpanners
