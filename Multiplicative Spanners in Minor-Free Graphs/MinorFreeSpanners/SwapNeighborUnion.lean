import MinorFreeSpanners.NewBadWitnessClassification
import MinorFreeSpanners.StarNeighborhoodUnion

/-! Transport the actual exchanged branches into the concrete original
neighbor-star union. This prepares induced-graph, rather than global-degree,
charges for the new bad forest-edge witnesses. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
variable {V : Type*} [Fintype V]
attribute [local instance] Classical.propDecidable

noncomputable def swapWitnessVertices (G : SimpleGraph V) (C : Finset V)
    (L : V → Finset V) (b u : V) : Finset V :=
  starHitUnion C L (G.neighborFinset u ∪ G.neighborFinset b)

omit [Fintype V] in
theorem branch_subset_starHitUnion (C : Finset V) (L : V → Finset V)
    (S : Finset V) {d x : V} (hd : d ∈ C) (hx : x ∈ S)
    (hxd : x ∈ insert d (L d)) : insert d (L d) ⊆ starHitUnion C L S := by
  intro y hy
  exact Finset.mem_biUnion.mpr ⟨d,Finset.mem_filter.mpr ⟨hd,x,hx,hxd⟩,hy⟩

/-- The domain consists of actual full old branches meeting either original
neighborhood. The two exchanged old branches lie in it because their
centers are both actual neighbors of the removed leaf. -/
theorem IsStarPacking.swapped_branch_subset_witness_vertices
    {G : SimpleGraph V} {A C : Finset V} {ell : ℕ} {L : V → Finset V}
    (h : IsStarPacking G A C ell L) {b c u v d : V}
    (hb : b ∈ C) (hc : c ∈ C) (hbc : b ≠ c) (hu : u ∈ L b) (hv : v ∈ L c)
    (hcu : G.Adj c u) (hd : d ∈ C)
    (hhit : G.Adj u d ∨ ∃ z ∈ MinorFreeSpanners.twoStarLeafSwap L u v d, G.Adj b z) :
    insert d (MinorFreeSpanners.twoStarLeafSwap L u v d) ⊆ swapWitnessVertices G C L b u := by
  classical
  have hcenter : ∀ e ∈ C, G.Adj u e → insert e (L e) ⊆ swapWitnessVertices G C L b u := by
    intro e he hue
    exact branch_subset_starHitUnion C L _ he
      (Finset.mem_union_left _ (by simpa using hue)) (Finset.mem_insert_self _ _)
  have hbb := hcenter b hb (h.2.2.1 b u hu).symm
  have hcc := hcenter c hc hcu.symm
  by_cases hdb : d=b
  · exact (h.twoStarLeafSwap_branch_subset hbc hu hv (Or.inl hdb)).trans
      (Finset.union_subset hbb hcc)
  · by_cases hdc : d=c
    · exact (h.twoStarLeafSwap_branch_subset hbc hu hv (Or.inr hdc)).trans
        (Finset.union_subset hbb hcc)
    · rw [h.twoStarLeafSwap_at_other hu hv hdb hdc]
      rcases hhit with hud | ⟨z,hz,hbz⟩
      · exact hcenter d hd hud
      · have hzold : z ∈ L d := by
          simpa only [h.twoStarLeafSwap_at_other hu hv hdb hdc] using hz
        exact branch_subset_starHitUnion C L _ hd
          (Finset.mem_union_right _ (by simpa using hbz)) (Finset.mem_insert_of_mem hzold)

/-- A new witness using the inserted forest edge (b,v) charges its other
center to a genuine neighbor of v inside the actual induced witness domain. -/
theorem IsStarPacking.inserted_left_witness_center_mem
    {G : SimpleGraph V} {A C : Finset V} {ell : ℕ} {L : V → Finset V}
    (h : IsStarPacking G A C ell L) {b c u v d z : V}
    (hb : b ∈ C) (hc : c ∈ C) (hbc : b ≠ c) (hu : u ∈ L b) (hv : v ∈ L c)
    (hcu : G.Adj c u)
    (hp : ((b,v),(d,z)) ∈ badForestPairs G C (MinorFreeSpanners.twoStarLeafSwap L u v)) :
    d ∈ swapWitnessVertices G C L b u ∧ G.Adj v d := by
  obtain ⟨_,hd,_,_,hz,hvd,hzb⟩ := (mem_badForestPairs G C _ b v d z).mp hp
  exact ⟨h.swapped_branch_subset_witness_vertices hb hc hbc hu hv hcu hd
    (Or.inr ⟨z,hz,hzb.symm⟩) (Finset.mem_insert_self _ _),hvd⟩

/-- A new witness using the other inserted forest edge (c,u) charges its
other forest leaf to a genuine induced-domain neighbor of c. -/
theorem IsStarPacking.inserted_right_witness_leaf_mem
    {G : SimpleGraph V} {A C : Finset V} {ell : ℕ} {L : V → Finset V}
    (h : IsStarPacking G A C ell L) {b c u v d z : V}
    (hb : b ∈ C) (hc : c ∈ C) (hbc : b ≠ c) (hu : u ∈ L b) (hv : v ∈ L c)
    (hcu : G.Adj c u)
    (hp : ((c,u),(d,z)) ∈ badForestPairs G C (MinorFreeSpanners.twoStarLeafSwap L u v)) :
    z ∈ swapWitnessVertices G C L b u ∧ G.Adj c z := by
  obtain ⟨_,hd,_,_,hz,hud,hzc⟩ := (mem_badForestPairs G C _ c u d z).mp hp
  exact ⟨h.swapped_branch_subset_witness_vertices hb hc hbc hu hv hcu hd
    (Or.inl hud) (Finset.mem_insert_of_mem hz),hzc.symm⟩

end MinorFreeSpanners
