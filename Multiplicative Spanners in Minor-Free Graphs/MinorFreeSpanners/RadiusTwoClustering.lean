import MinorFreeSpanners.DisjointNeighborhoodPacking

/-! Actual radius-two groups, including the original disjoint closed stars.
No partition or assignment is supplied to the existence theorem. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

/-- Every eligible vertex is covered. Each branch retains the complete closed
neighborhood of its center, and each added vertex has an edge into that core. -/
theorem exists_radius_two_clustering {V : Type*} [Fintype V]
    (G : SimpleGraph V) (S : Finset V) :
    ∃ C : Finset V, ∃ B : V → Finset V,
      C ⊆ S ∧
      (∀ c∈C, closedNeighborhood G c ⊆ B c) ∧
      (∀ c∈C, ∀ c'∈C, c ≠ c' → Disjoint (B c) (B c')) ∧
      C.biUnion B = C.biUnion (closedNeighborhood G) ∪ S ∧
      (∀ c∈C, ∀ v∈B c, v∈closedNeighborhood G c ∨
        ∃ u∈closedNeighborhood G c, G.Adj v u) := by
  classical
  obtain ⟨C,hCS,hdis,hcover⟩ := exists_disjoint_neighborhood_packing G S
  let W := C.biUnion (closedNeighborhood G)
  let M := W ∪ S
  let R (v c : V) := c∈C ∧ (v∈closedNeighborhood G c ∨
    (v∉W ∧ ∃ u∈closedNeighborhood G c, G.Adj v u))
  have hex (v : V) (hv : v∈M) : ∃ c, R v c := by
    by_cases hw : v∈W
    · obtain ⟨c,hc,hv⟩ := Finset.mem_biUnion.mp hw
      exact ⟨c,hc,Or.inl hv⟩
    · have hs : v∈S := (Finset.mem_union.mp hv).resolve_left hw
      obtain ⟨u,hu,hadj⟩ := hcover v hs hw
      obtain ⟨c,hc,hu⟩ := Finset.mem_biUnion.mp hu
      exact ⟨c,hc,Or.inr ⟨hw,u,hu,hadj⟩⟩
  let owner (v : V) : V := if hv : v∈M then Classical.choose (hex v hv) else v
  have howner (v : V) (hv : v∈M) : R v (owner v) := by
    simpa only [owner,dite_eq_left hv] using Classical.choose_spec (hex v hv)
  let B (c : V) := M.filter (fun v => owner v = c)
  have hmem (v c : V) : v∈B c ↔ v∈M ∧ owner v = c := Finset.mem_filter
  have hcore (c : V) (hc : c∈C) : closedNeighborhood G c ⊆ B c := by
    intro v hv
    have hw : v∈W := Finset.mem_biUnion.mpr ⟨c,hc,hv⟩
    have hm : v∈M := Finset.mem_union_left _ hw
    have ho := howner v hm
    have hov : v∈closedNeighborhood G (owner v) := ho.2.resolve_right (by
      intro hh
      exact hh.1 hw)
    have heq : owner v = c := by
      by_contra hn
      exact Finset.disjoint_left.mp (hdis (owner v) ho.1 c hc hn) hov hv
    exact (hmem v c).mpr ⟨hm,heq⟩
  refine ⟨C,B,hCS,hcore,?_,?_,?_⟩
  · intro c _ c' _ hne
    apply Finset.disjoint_left.mpr
    intro v hv hv'
    exact hne (((hmem v c).mp hv).2.symm.trans ((hmem v c').mp hv').2)
  · change C.biUnion B = M
    apply Finset.Subset.antisymm
    · intro v hv
      obtain ⟨c,_,hv⟩ := Finset.mem_biUnion.mp hv
      exact ((hmem v c).mp hv).1
    · intro v hv
      exact Finset.mem_biUnion.mpr ⟨owner v,(howner v hv).1,
        (hmem v (owner v)).mpr ⟨hv,rfl⟩⟩
  · intro c _ v hv
    obtain ⟨hm,he⟩ := (hmem v c).mp hv
    have ho := (howner v hm).2
    rw [he] at ho
    exact ho.imp_right And.right

end MinorFreeSpanners
