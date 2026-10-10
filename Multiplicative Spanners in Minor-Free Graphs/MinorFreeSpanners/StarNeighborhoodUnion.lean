import MinorFreeSpanners.StarPackingMinor

/-! Bound the actual union of stars meeting a specified finite vertex set.
The neighbor-union specialization supplies the real induced witness domain
used in the local swap argument; no density conclusion is assumed. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- The actual selected centers whose branch meets S. -/
def starHitCenters (C : Finset V) (L : V → Finset V) (S : Finset V) : Finset V :=
  C.filter fun b => ∃ x ∈ S, x ∈ insert b (L b)

/-- The actual covered vertices of all selected stars meeting S. -/
def starHitUnion (C : Finset V) (L : V → Finset V) (S : Finset V) : Finset V :=
  (starHitCenters C L S).biUnion fun b => insert b (L b)

omit [Fintype V] in
/-- Branch disjointness assigns distinct meeting vertices to distinct stars. -/
theorem IsStarPacking.starHitCenters_card {G : SimpleGraph V} {A C : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A C ell L)
    (hAC : Disjoint A C) (S : Finset V) :
    (starHitCenters C L S).card ≤ S.card := by
  classical
  have hex : ∀ b : starHitCenters C L S, ∃ x : S, x.val ∈ insert b.val (L b.val) := by
    intro b
    obtain ⟨x,hx,hxb⟩ := (Finset.mem_filter.mp b.property).2
    exact ⟨⟨x,hx⟩,hxb⟩
  choose f hf using hex
  apply Finset.card_le_card_of_injective (f := f)
  intro b c he
  apply Subtype.ext
  by_contra hbc
  exact Finset.disjoint_left.mp (h.branch_disjoint hAC
    (Finset.mem_filter.mp b.property).1 (Finset.mem_filter.mp c.property).1 hbc)
    (hf b) (by simpa only [he] using hf c)

omit [Fintype V] in
/-- Count a real union, allowing partially filled stars and empty S. -/
theorem IsStarPacking.starHitUnion_card {G : SimpleGraph V} {A C : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A C ell L)
    (hAC : Disjoint A C) (S : Finset V) :
    (starHitUnion C L S).card ≤ (ell+1)*S.card := by
  classical
  calc
    _ ≤ ∑ b ∈ starHitCenters C L S, (insert b (L b)).card := Finset.card_biUnion_le
    _ ≤ ∑ _b ∈ starHitCenters C L S, (ell+1) := by
      apply Finset.sum_le_sum
      intro b _
      exact (Finset.card_insert_le b (L b)).trans (Nat.add_le_add_right (h.2.2.2.2.2 b) 1)
    _ = (ell+1)*(starHitCenters C L S).card := by simp [Nat.mul_comm]
    _ ≤ _ := Nat.mul_le_mul_left _ (h.starHitCenters_card hAC S)

/-- The precise real-graph neighborhood union bound needed for an induced
small witness: at most (ell+1) times the two actual vertex degrees. -/
theorem IsStarPacking.neighbor_star_union_card {G : SimpleGraph V} {A C : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A C ell L)
    (hAC : Disjoint A C) (u v : V) :
    (starHitUnion C L (G.neighborFinset u ∪ G.neighborFinset v)).card ≤
      (ell+1)*(G.degree u+G.degree v) := by
  refine (h.starHitUnion_card hAC _).trans (Nat.mul_le_mul_left _ ?_)
  exact (Finset.card_union_le _ _).trans_eq (by simp)

end MinorFreeSpanners
