import MinorFreeSpanners.MateAugmentation

/-! Actual mate-free full-star selection. The unmated specialization states
its left-small-vertex hypothesis explicitly; minimum degree alone does not
supply an upper degree bound. -/
namespace MinorFreeSpanners
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Augment, select independent leaves, and return to the actual original
bipartite graph. All mate and boundary counts are literal finite counts. -/
theorem exists_mate_free_star_selection (G : SimpleGraph V) (A B : Finset V)
    (ell dA dB : ℕ) (q : ℝ)
    (hG : G.IsBipartiteWith (A:Set V) (B:Set V)) (hq : 0 < q)
    (hsize : ell*B.card ≤ A.card) (hdeg : dA < dB)
    (hmates : ∀ x ∈ A, ((Finset.univ : Finset V).filter fun z =>
      q ≤ (Fintype.card (G.commonNeighbors x z):ℝ)).card ≤ dA)
    (hB : ∀ x ∈ A, dB ≤ (B.filter fun b => G.Adj x b).card) :
    ∃ C : Finset V, ∃ L : V → Finset V,
      C ⊆ B ∧ IsStarPacking G A C ell L ∧
      (∀ b ∈ C, (L b).card = ell) ∧
      (∀ b ∈ C, MateFreeOn G q (insert b (L b:Set V))) ∧
      (∀ w ∈ C.biUnion L, ((B \ C).filter fun b => G.Adj w b).card ≤ dA) ∧
      (A.Nonempty → C.Nonempty) := by
  classical
  let H := mateAugmentation G A q
  have hHA : ∀ x ∈ A, (A.filter fun z => H.Adj x z).card ≤ dA := by
    intro x hx
    exact (mateAugmentation_left_degree hG hx).trans (hmates x hx)
  have hHB : ∀ x ∈ A, dB ≤ (B.filter fun b => H.Adj x b).card := by
    intro x hx
    apply (hB x hx).trans
    apply Finset.card_le_card
    intro b hb
    obtain ⟨hb,he⟩ := Finset.mem_filter.mp hb
    exact Finset.mem_filter.mpr ⟨hb,Or.inl he⟩
  obtain ⟨C,L,hCB,hL,hfull,hbound,hne⟩ :=
    exists_full_star_selection H A B ell dA dB hsize hdeg hHA hHB
  obtain ⟨hLG,hfree⟩ := mateAugmentation_packing hG hq hCB hL
  refine ⟨C,L,hCB,hLG,hfull,hfree,?_,hne⟩
  intro w hw
  apply le_trans ?_ (hbound w hw)
  apply Finset.card_le_card
  intro b hb
  obtain ⟨hb,he⟩ := Finset.mem_filter.mp hb
  exact Finset.mem_filter.mpr ⟨hb,Or.inl he⟩

/-- The exact real unmated budget, with the necessary left-small domain
explicit. Prior regularization and subgraph-unmated lemmas supply this domain. -/
theorem unmated_small_left_star_selection (G : SimpleGraph V) (A B : Finset V)
    (ell d : ℕ) (K eps1 eps2 : ℝ)
    (hG : G.IsBipartiteWith (A:Set V) (B:Set V)) (hd : 0 < d)
    (he1 : 0 ≤ eps1) (he1' : eps1 < 1) (he2 : 0 < eps2)
    (hsize : ell*B.card ≤ A.card)
    (hsmall : ∀ x ∈ A, (G.degree x:ℝ) ≤ K*d)
    (hunmated : Unmated G K eps1 eps2 d)
    (hB : ∀ x ∈ A, d ≤ (B.filter fun b => G.Adj x b).card) :
    ∃ C : Finset V, ∃ L : V → Finset V,
      C ⊆ B ∧ IsStarPacking G A C ell L ∧
      (∀ b ∈ C, (L b).card = ell) ∧
      (∀ b ∈ C, MateFreeOn G (eps2*d) (insert b (L b:Set V))) ∧
      (∀ w ∈ C.biUnion L,
        (((B \ C).filter fun b => G.Adj w b).card:ℝ) ≤ eps1*d) ∧
      (A.Nonempty → C.Nonempty) := by
  classical
  have hdR : (0:ℝ) < d := Nat.cast_pos.mpr hd
  have heprod : 0 ≤ eps1*d := mul_nonneg he1 hdR.le
  have hfloor : ⌊eps1*(d:ℝ)⌋₊ < d :=
    (Nat.floor_lt heprod).mpr (by nlinarith)
  have hmates : ∀ x ∈ A, ((Finset.univ : Finset V).filter fun z =>
      eps2*d ≤ (Fintype.card (G.commonNeighbors x z):ℝ)).card ≤ ⌊eps1*(d:ℝ)⌋₊ := by
    intro x hx
    exact Nat.le_floor (hunmated x (hsmall x hx)).le
  obtain ⟨C,L,hCB,hL,hfull,hfree,hbound,hne⟩ :=
    exists_mate_free_star_selection G A B ell ⌊eps1*(d:ℝ)⌋₊ d (eps2*d)
      hG (mul_pos he2 hdR) hsize hfloor hmates hB
  refine ⟨C,L,hCB,hL,hfull,hfree,?_,hne⟩
  intro w hw
  exact (Nat.cast_le.mpr (hbound w hw)).trans (Nat.floor_le heprod)

end MinorFreeSpanners
