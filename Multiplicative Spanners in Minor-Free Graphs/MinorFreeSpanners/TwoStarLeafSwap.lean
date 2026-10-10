import MinorFreeSpanners.StarPackingMinor

/-! A concrete two-leaf exchange. All adjacency and mate-freeness statements
refer to the original graph. No optimality or cleaning conclusion is assumed. -/
namespace MinorFreeSpanners
open SimpleGraph
variable {V : Type*} [DecidableEq V]

/-- Exchange the two leaf labels in every assignment. Disjointness below
proves that this changes exactly the two specified owner stars. -/
def twoStarLeafSwap (L : V → Finset V) (u v : V) (d : V) : Finset V :=
  (L d).image (Equiv.swap u v)

theorem mem_twoStarLeafSwap {L : V → Finset V} {u v d x : V} :
    x ∈ twoStarLeafSwap L u v d ↔ Equiv.swap u v x ∈ L d := by
  constructor
  · intro hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    simpa using hy
  · intro hx
    exact Finset.mem_image.mpr ⟨Equiv.swap u v x,hx,by simp⟩

theorem twoStarLeafSwap_card (L : V → Finset V) (u v d : V) :
    (twoStarLeafSwap L u v d).card = (L d).card :=
  Finset.card_image_of_injective _ (Equiv.swap u v).injective

variable {G : SimpleGraph V} {A B C : Finset V} {ell : ℕ}
  {L : V → Finset V} {b c u v : V}

omit [DecidableEq V] in
theorem IsStarPacking.leaf_owner_unique (h : IsStarPacking G A C ell L)
    {d e x : V} (hd : x ∈ L d) (he : x ∈ L e) : d = e := by
  by_contra hde
  exact Finset.disjoint_left.mp (h.2.2.2.2.1 d e hde) hd he

omit [DecidableEq V] in
theorem IsStarPacking.swap_leaves_ne (h : IsStarPacking G A C ell L)
    (hbc : b ≠ c) (hu : u ∈ L b) (hv : v ∈ L c) : u ≠ v := by
  intro huv
  subst v
  exact hbc (h.leaf_owner_unique hu hv)

theorem IsStarPacking.twoStarLeafSwap_at_left (h : IsStarPacking G A C ell L)
    (hbc : b ≠ c) (hu : u ∈ L b) (hv : v ∈ L c) :
    twoStarLeafSwap L u v b = insert v ((L b).erase u) := by
  have hvb : v ∉ L b := fun hmem => hbc (h.leaf_owner_unique hmem hv)
  have huv := h.swap_leaves_ne hbc hu hv
  ext x
  rw [mem_twoStarLeafSwap]
  by_cases hxu : x = u
  · subst x; simp [huv,hvb]
  · by_cases hxv : x = v
    · subst x; simp [hu]
    · simp [Equiv.swap_apply_of_ne_of_ne hxu hxv,hxu,hxv]

theorem IsStarPacking.twoStarLeafSwap_at_right (h : IsStarPacking G A C ell L)
    (hbc : b ≠ c) (hu : u ∈ L b) (hv : v ∈ L c) :
    twoStarLeafSwap L u v c = insert u ((L c).erase v) := by
  simpa [twoStarLeafSwap,Equiv.swap_comm u v] using
    h.twoStarLeafSwap_at_left hbc.symm hv hu

theorem IsStarPacking.twoStarLeafSwap_at_other (h : IsStarPacking G A C ell L)
    (hu : u ∈ L b) (hv : v ∈ L c) {d : V} (hdb : d ≠ b) (hdc : d ≠ c) :
    twoStarLeafSwap L u v d = L d := by
  have hud : u ∉ L d := fun hx => hdb (h.leaf_owner_unique hx hu)
  have hvd : v ∉ L d := fun hx => hdc (h.leaf_owner_unique hx hv)
  ext x
  rw [mem_twoStarLeafSwap]
  by_cases hxu : x = u
  · subst x; simp [hud,hvd]
  · by_cases hxv : x = v
    · subst x; simp [hud,hvd]
    · rw [Equiv.swap_apply_of_ne_of_ne hxu hxv]

/-- Genuine cross edges make the swapped assignments a valid induced-star
packing. Independence follows from the actual bipartition. -/
theorem IsStarPacking.twoStarLeafSwap_valid (h : IsStarPacking G A C ell L)
    (hG : G.IsBipartiteWith (A : Set V) (B : Set V))
    (hu : u ∈ L b) (hv : v ∈ L c) (hbv : G.Adj b v) (hcu : G.Adj c u) :
    IsStarPacking G A C ell (twoStarLeafSwap L u v) := by
  have hs : ∀ d, twoStarLeafSwap L u v d ⊆ A := by
    intro d x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    by_cases hyu : y = u
    · subst y; simpa using h.2.1 c hv
    · by_cases hyv : y = v
      · subst y; simpa using h.2.1 b hu
      · simpa [Equiv.swap_apply_of_ne_of_ne hyu hyv] using h.2.1 d hy
  refine ⟨?_,hs,?_,?_,?_,?_⟩
  · intro d hd
    simp [twoStarLeafSwap,h.1 d hd]
  · intro d x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    by_cases hyu : y = u
    · subst y
      have hdb := h.leaf_owner_unique hy hu
      subst d; simpa using hbv
    · by_cases hyv : y = v
      · subst y
        have hdc := h.leaf_owner_unique hy hv
        subst d; simpa using hcu
      · simpa [Equiv.swap_apply_of_ne_of_ne hyu hyv] using h.2.2.1 d y hy
  · intro d x hx y hy _ he
    exact Set.disjoint_left.mp hG.disjoint (hs d hy)
      (hG.mem_of_mem_adj (hs d hx) he)
  · intro d e hde
    apply Finset.disjoint_left.mpr
    intro x hd he
    exact Finset.disjoint_left.mp (h.2.2.2.2.1 d e hde)
      (mem_twoStarLeafSwap.mp hd) (mem_twoStarLeafSwap.mp he)
  · intro d
    rw [twoStarLeafSwap_card]
    exact h.2.2.2.2.2 d

/-- The covered leaf set is literally unchanged. -/
theorem twoStarLeafSwap_leaf_union (hb : b ∈ C) (hc : c ∈ C)
    (hu : u ∈ L b) (hv : v ∈ L c) :
    C.biUnion (twoStarLeafSwap L u v) = C.biUnion L := by
  ext x
  constructor
  · intro hx
    obtain ⟨d,hd,hx⟩ := Finset.mem_biUnion.mp hx
    by_cases hxu : x = u
    · subst x; exact Finset.mem_biUnion.mpr ⟨b,hb,hu⟩
    · by_cases hxv : x = v
      · subst x; exact Finset.mem_biUnion.mpr ⟨c,hc,hv⟩
      · exact Finset.mem_biUnion.mpr ⟨d,hd,by
          simpa [Equiv.swap_apply_of_ne_of_ne hxu hxv] using mem_twoStarLeafSwap.mp hx⟩
  · intro hx
    obtain ⟨d,hd,hx⟩ := Finset.mem_biUnion.mp hx
    by_cases hxu : x = u
    · subst x
      exact Finset.mem_biUnion.mpr ⟨c,hc,mem_twoStarLeafSwap.mpr (by simpa using hv)⟩
    · by_cases hxv : x = v
      · subst x
        exact Finset.mem_biUnion.mpr ⟨b,hb,mem_twoStarLeafSwap.mpr (by simpa using hu)⟩
      · exact Finset.mem_biUnion.mpr ⟨d,hd,mem_twoStarLeafSwap.mpr (by
          simpa [Equiv.swap_apply_of_ne_of_ne hxu hxv] using hx)⟩

/-- The covered vertex set, including all centers, is literally unchanged. -/
theorem twoStarLeafSwap_vertex_union (hb : b ∈ C) (hc : c ∈ C)
    (hu : u ∈ L b) (hv : v ∈ L c) :
    (C.biUnion fun d => insert d (twoStarLeafSwap L u v d)) =
      C.biUnion fun d => insert d (L d) := by
  have union_eq (N : V → Finset V) :
      (C.biUnion fun d => insert d (N d)) = C ∪ C.biUnion N := by
    ext x
    simp only [Finset.mem_biUnion,Finset.mem_insert,Finset.mem_union]
    aesop
  rw [union_eq,union_eq,twoStarLeafSwap_leaf_union hb hc hu hv]

/-- Each changed branch lies inside the explicit union of the two old
branches. This is the precise premise needed for mate-freeness transfer. -/
theorem IsStarPacking.twoStarLeafSwap_branch_subset (h : IsStarPacking G A C ell L)
    (hbc : b ≠ c) (hu : u ∈ L b) (hv : v ∈ L c) {d : V} (hd : d = b ∨ d = c) :
    insert d (twoStarLeafSwap L u v d) ⊆ insert b (L b) ∪ insert c (L c) := by
  rcases hd with rfl | rfl
  · rw [h.twoStarLeafSwap_at_left hbc hu hv]
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_erase,Finset.mem_union] at hx ⊢
    aesop
  · rw [h.twoStarLeafSwap_at_right hbc hu hv]
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_erase,Finset.mem_union] at hx ⊢
    aesop

/-- The nonmate premise concerns actual common neighbors in the ORIGINAL
host graph, including pairs across the two old branches. -/
theorem IsStarPacking.twoStarLeafSwap_mateFree [Fintype V]
    (h : IsStarPacking G A C ell L) (hbc : b ≠ c) (hu : u ∈ L b) (hv : v ∈ L c)
    {q : ℝ} (hold : ∀ d ∈ C, MateFreeOn G q (↑(insert d (L d)) : Set V))
    (hpair : MateFreeOn G q (↑(insert b (L b) ∪ insert c (L c)) : Set V)) :
    ∀ d ∈ C, MateFreeOn G q (↑(insert d (twoStarLeafSwap L u v d)) : Set V) := by
  intro d hd
  by_cases hdb : d = b
  · exact hpair.subset (h.twoStarLeafSwap_branch_subset hbc hu hv (Or.inl hdb))
  · by_cases hdc : d = c
    · exact hpair.subset (h.twoStarLeafSwap_branch_subset hbc hu hv (Or.inr hdc))
    · rw [h.twoStarLeafSwap_at_other hu hv hdb hdc]
      exact hold d hd

/-- A bundled finite two-star exchange with actual cross edges and explicit
original-host nonmates. The selected centers remain on the opposite side. -/
theorem IsStarPacking.twoStarLeafSwap [Fintype V]
    (h : IsStarPacking G A C ell L) (hG : G.IsBipartiteWith (A : Set V) (B : Set V))
    (hCB : C ⊆ B) (hb : b ∈ C) (hc : c ∈ C) (hbc : b ≠ c)
    (hu : u ∈ L b) (hv : v ∈ L c) (hbv : G.Adj b v) (hcu : G.Adj c u)
    {q : ℝ} (hold : ∀ d ∈ C, MateFreeOn G q (↑(insert d (L d)) : Set V))
    (hpair : MateFreeOn G q (↑(insert b (L b) ∪ insert c (L c)) : Set V)) :
    let M := twoStarLeafSwap L u v
    IsStarPacking G A C ell M ∧ (∀ d, (M d).card = (L d).card) ∧
    C.biUnion M = C.biUnion L ∧
    (C.biUnion fun d => insert d (M d)) = (C.biUnion fun d => insert d (L d)) ∧
    (∀ d ∈ C, MateFreeOn G q (↑(insert d (M d)) : Set V)) ∧
    (∀ d ∈ C, ∀ e ∈ C, d ≠ e → Disjoint (insert d (M d)) (insert e (M e))) := by
  dsimp only
  have hM := h.twoStarLeafSwap_valid hG hu hv hbv hcu
  refine ⟨hM,twoStarLeafSwap_card L u v,twoStarLeafSwap_leaf_union hb hc hu hv,
    twoStarLeafSwap_vertex_union hb hc hu hv,h.twoStarLeafSwap_mateFree hbc hu hv hold hpair,?_⟩
  intro d hd e he hde
  apply hM.branch_disjoint _ hd he hde
  exact (Finset.disjoint_coe.mp hG.disjoint).mono_right hCB

end MinorFreeSpanners
