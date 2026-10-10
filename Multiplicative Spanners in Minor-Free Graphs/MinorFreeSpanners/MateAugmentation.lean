import MinorFreeSpanners.StarPackingMinor

/-! Actual addition of left-side mate edges. Independent selected leaves
then become genuinely mate-free in the original bipartite graph. -/
namespace MinorFreeSpanners
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Add exactly the distinct mate pairs inside A to the actual host graph. -/
noncomputable def mateAugmentation (G : SimpleGraph V) (A : Finset V) (q : ℝ) :
    SimpleGraph V where
  Adj x y := G.Adj x y ∨ (x ∈ A ∧ y ∈ A ∧ x ≠ y ∧
    q ≤ (Fintype.card (G.commonNeighbors x y) : ℝ))
  symm := ⟨by
    intro x y he
    rcases he with he|⟨hx,hy,hne,hq⟩
    · exact Or.inl he.symm
    · exact Or.inr ⟨hy,hx,hne.symm,by simpa only [G.commonNeighbors_symm y x] using hq⟩⟩
  loopless := ⟨by intro x he; exact he.elim (fun h => h.ne rfl) (fun h => h.2.2.1 rfl)⟩

omit [DecidableEq V] in
/-- Every old host edge is retained literally. -/
theorem le_mateAugmentation (G : SimpleGraph V) (A : Finset V) (q : ℝ) :
    G ≤ mateAugmentation G A q := fun _ _ he => Or.inl he

omit [DecidableEq V] in
/-- No new edge touches a vertex outside the left side. -/
theorem mateAugmentation_adj_right {G : SimpleGraph V} {A : Finset V} {q : ℝ}
    {x b : V} (hb : b ∉ A) :
    (mateAugmentation G A q).Adj x b ↔ G.Adj x b := by
  constructor
  · rintro (he|he)
    · exact he
    · exact (hb he.2.1).elim
  · exact Or.inl

omit [DecidableEq V] in
/-- Internal left neighbors in the augmented graph inject into actual mates. -/
theorem mateAugmentation_left_degree {G : SimpleGraph V} {A B : Finset V} {q : ℝ}
    (hG : G.IsBipartiteWith (A:Set V) (B:Set V)) {x : V} (hx : x ∈ A) :
    (A.filter fun z => (mateAugmentation G A q).Adj x z).card ≤
      ((Finset.univ : Finset V).filter fun z =>
        q ≤ (Fintype.card (G.commonNeighbors x z) : ℝ)).card := by
  apply Finset.card_le_card
  intro z hz
  obtain ⟨hzA,he⟩ := Finset.mem_filter.mp hz
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
  rcases he with he|he
  · exact (Set.disjoint_left.mp hG.disjoint hzA (hG.mem_of_mem_adj hx he)).elim
  · exact he.2.2.2

/-- Every star chosen independently in the augmented graph is an actual
original-graph star, with genuine mate-free branch vertices. -/
theorem mateAugmentation_packing {G : SimpleGraph V} {A B C : Finset V} {q : ℝ}
    {ell : ℕ} {L : V → Finset V}
    (hG : G.IsBipartiteWith (A:Set V) (B:Set V)) (hq : 0 < q)
    (hCB : C ⊆ B) (h : IsStarPacking (mateAugmentation G A q) A C ell L) :
    IsStarPacking G A C ell L ∧
      ∀ b ∈ C, MateFreeOn G q (insert b (L b : Set V)) := by
  classical
  have hold : ∀ b a, a ∈ L b → G.Adj b a := by
    intro b a ha
    have hbC : b ∈ C := by
      by_contra hb; simp [h.1 b hb] at ha
    have hbA : b ∉ A := fun hb => Set.disjoint_left.mp hG.disjoint hb (hCB hbC)
    exact (mateAugmentation_adj_right hbA).mp (h.2.2.1 b a ha).symm |>.symm
  refine ⟨⟨h.1,h.2.1,hold,?_,h.2.2.2.2.1,h.2.2.2.2.2⟩,?_⟩
  · intro b x hx y hy hxy he
    exact h.2.2.2.1 b x hx y hy hxy (Or.inl he)
  · intro b hb
    apply MateFreeOn.insert_center hG (h.2.1 b) ?_ hq (hCB hb)
    intro x hx y hy hxy
    apply lt_of_not_ge
    intro hmates
    exact h.2.2.2.1 b x hx y hy hxy (Or.inr ⟨h.2.1 b hx,h.2.1 b hy,hxy,hmates⟩)

end MinorFreeSpanners
