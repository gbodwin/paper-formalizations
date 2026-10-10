import MinorFreeSpanners.SwapNeighborUnion

/-! Inject actual inserted-edge bad witnesses into neighbors in the actual
induced witness graph. The two charges use centers and leaves respectively,
with branch ownership proving the latter injection. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
variable {V : Type*} [Fintype V]
attribute [local instance] Classical.propDecidable

variable {G : SimpleGraph V} {A B C : Finset V} {ell : ℕ}
  {L : V → Finset V} {b c u v : V}

theorem swapWitnessVertices_partner_mem (hc : c ∈ C) (hv : v ∈ L c)
    (hcu : G.Adj c u) :
    c ∈ swapWitnessVertices G C L b u ∧ v ∈ swapWitnessVertices G C L b u := by
  have hs := branch_subset_starHitUnion C L
    (G.neighborFinset u ∪ G.neighborFinset b) hc
    (Finset.mem_union_left _ (by simpa using hcu.symm)) (Finset.mem_insert_self c (L c))
  exact ⟨hs (Finset.mem_insert_self _ _),hs (Finset.mem_insert_of_mem hv)⟩

/-- Each actual bad witness at inserted edge (b,v) gives a different
neighboring center inside the concrete induced graph. -/
theorem IsStarPacking.inserted_left_witness_count
    (h : IsStarPacking G A C ell L) (hb : b ∈ C) (hc : c ∈ C)
    (hbc : b ≠ c) (hu : u ∈ L b) (hv : v ∈ L c) (hcu : G.Adj c u) :
    (badForestOutgoing G C (MinorFreeSpanners.twoStarLeafSwap L u v) b v).card ≤
      (G.induce (swapWitnessVertices G C L b u : Set V)).degree
        ⟨v,(swapWitnessVertices_partner_mem hc hv hcu).2⟩ := by
  classical
  let M := MinorFreeSpanners.twoStarLeafSwap L u v
  let H := swapWitnessVertices G C L b u
  let S := badForestOutgoing G C M b v
  let vv : (H : Set V) := ⟨v,(swapWitnessVertices_partner_mem hc hv hcu).2⟩
  have him : ∀ p ∈ S, p.2.1 ∈ H ∧ G.Adj v p.2.1 := by
    intro p hp
    obtain ⟨hp,he⟩ := Finset.mem_filter.mp hp
    rcases p with ⟨⟨a,x⟩,⟨d,z⟩⟩
    cases he
    exact h.inserted_left_witness_center_mem hb hc hbc hu hv hcu hp
  let f : S → (G.induce (H : Set V)).neighborSet vv := fun p =>
    ⟨⟨p.val.2.1,(him p.val p.property).1⟩,(him p.val p.property).2⟩
  have hinj : Function.Injective f := by
    intro p q he
    have hcenter : p.val.2.1=q.val.2.1 := congrArg (fun x => x.val.val) he
    have hp := Finset.mem_filter.mp p.property
    have hq := Finset.mem_filter.mp q.property
    have hfirst : p.val.1=q.val.1 := hp.2.trans hq.2.symm
    have hmemQ : ((p.val.1.1,p.val.1.2),(p.val.2.1,q.val.2.2)) ∈ badForestPairs G C M := by
      simpa only [hfirst,hcenter] using hq.1
    have hleaves := badForestPairs_eq_of_centers G C M hp.1 hmemQ
    apply Subtype.ext
    exact Prod.ext hfirst (Prod.ext hcenter hleaves.2)
  calc
    S.card = Fintype.card S := (Fintype.card_coe _).symm
    _ ≤ Fintype.card ((G.induce (H : Set V)).neighborSet vv) := Fintype.card_le_of_injective f hinj
    _ = _ := SimpleGraph.card_neighborSet_eq_degree _ _

/-- Each bad witness at inserted edge (c,u) gives a different neighboring
leaf inside the concrete induced graph. Actual owner uniqueness, rather
than an assumed distinctness condition, proves the injection. -/
theorem IsStarPacking.inserted_right_witness_count
    (h : IsStarPacking G A C ell L)
    (hG : G.IsBipartiteWith (A : Set V) (B : Set V))
    (hb : b ∈ C) (hc : c ∈ C) (hbc : b ≠ c) (hu : u ∈ L b) (hv : v ∈ L c)
    (hbv : G.Adj b v) (hcu : G.Adj c u) :
    (badForestOutgoing G C (MinorFreeSpanners.twoStarLeafSwap L u v) c u).card ≤
      (G.induce (swapWitnessVertices G C L b u : Set V)).degree
        ⟨c,(swapWitnessVertices_partner_mem hc hv hcu).1⟩ := by
  classical
  let M := MinorFreeSpanners.twoStarLeafSwap L u v
  let H := swapWitnessVertices G C L b u
  let S := badForestOutgoing G C M c u
  let cc : (H : Set V) := ⟨c,(swapWitnessVertices_partner_mem hc hv hcu).1⟩
  have hM := h.twoStarLeafSwap_valid hG hu hv hbv hcu
  have him : ∀ p ∈ S, p.2.2 ∈ H ∧ G.Adj c p.2.2 := by
    intro p hp
    obtain ⟨hp,he⟩ := Finset.mem_filter.mp hp
    rcases p with ⟨⟨a,x⟩,⟨d,z⟩⟩
    cases he
    exact h.inserted_right_witness_leaf_mem hb hc hbc hu hv hcu hp
  let f : S → (G.induce (H : Set V)).neighborSet cc := fun p =>
    ⟨⟨p.val.2.2,(him p.val p.property).1⟩,(him p.val p.property).2⟩
  have hinj : Function.Injective f := by
    intro p q he
    have hleaf : p.val.2.2=q.val.2.2 := congrArg (fun x => x.val.val) he
    have hp := Finset.mem_filter.mp p.property
    have hq := Finset.mem_filter.mp q.property
    have hpM := (mem_badForestPairs G C M _ _ _ _).mp hp.1
    have hqM := (mem_badForestPairs G C M _ _ _ _).mp hq.1
    have hcenter : p.val.2.1=q.val.2.1 := hM.leaf_owner_unique hpM.2.2.2.2.1
      (by simpa only [hleaf] using hqM.2.2.2.2.1)
    apply Subtype.ext
    exact Prod.ext (hp.2.trans hq.2.symm) (Prod.ext hcenter hleaf)
  calc
    S.card = Fintype.card S := (Fintype.card_coe _).symm
    _ ≤ Fintype.card ((G.induce (H : Set V)).neighborSet cc) := Fintype.card_le_of_injective f hinj
    _ = _ := SimpleGraph.card_neighborSet_eq_degree _ _

end MinorFreeSpanners
