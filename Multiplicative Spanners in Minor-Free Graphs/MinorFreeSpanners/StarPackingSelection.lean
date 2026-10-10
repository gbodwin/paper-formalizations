import MinorFreeSpanners.StarConflictCount

/-! Actual selection of full induced stars with the Postle boundary budget. -/
namespace MinorFreeSpanners
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- Disjoint selected leaves have their literal summed cardinality. -/
theorem IsStarPacking.size_eq_sum {G : SimpleGraph V} {A B : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A B ell L) :
    starPackingSize B L = ∑ b ∈ B, (L b).card := by
  apply Finset.card_biUnion
  intro b _ c _ hbc
  exact h.2.2.2.2.1 b c hbc

omit [Fintype V] in
/-- If all A is covered and A is large enough, every center must be full. -/
theorem IsStarPacking.full_of_cover {G : SimpleGraph V} {A B : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A B ell L)
    (hsize : ell*B.card ≤ A.card) (hcover : B.biUnion L = A) :
    ∀ b ∈ B, (L b).card = ell := by
  have he : starPackingSize B L = ell*B.card := by
    apply Nat.le_antisymm h.size_le
    simpa only [starPackingSize,hcover] using hsize
  have hs : (∑ b ∈ B, (L b).card) = ∑ _b ∈ B, ell := by
    rw [← h.size_eq_sum,he]
    simp [Nat.mul_comm]
  exact (Finset.sum_eq_sum_iff_of_le (fun b _ => h.2.2.2.2.2 b)).mp hs

omit [Fintype V] in
/-- Restrict the literal assignment to an actual subset of centers. -/
theorem IsStarPacking.restrict_centers {G : SimpleGraph V} {A B C : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A B ell L) :
    IsStarPacking G A C ell (fun b => if b ∈ C then L b else ∅) := by
  classical
  let M := fun b => if b ∈ C then L b else ∅
  have hML : ∀ b, M b ⊆ L b := by intro b; dsimp [M]; split <;> simp
  have hh := h.leaf_subset hML
  refine ⟨?_,hh.2.1,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2.1,hh.2.2.2.2.2⟩
  intro b hb
  simp [hb]

omit [Fintype V] in
/-- Restricting center assignments does not change the selected leaf union. -/
theorem restrict_star_union {C : Finset V} {L : V → Finset V} :
    C.biUnion (fun b => if b ∈ C then L b else ∅) = C.biUnion L := by
  classical
  apply Finset.biUnion_congr rfl
  intro b hb
  simp [hb]

/-- Postle's full-star selection, from an internally selected maximum packing.
The bound uses actual graph-neighbor counts and an actual finite star family. -/
theorem exists_full_star_selection (G : SimpleGraph V) (A B : Finset V)
    (ell dA dB : ℕ) (hsize : ell*B.card ≤ A.card) (hdeg : dA < dB)
    (hA : ∀ x ∈ A, (A.filter fun z => G.Adj x z).card ≤ dA)
    (hB : ∀ x ∈ A, dB ≤ (B.filter fun b => G.Adj x b).card) :
    ∃ C : Finset V, ∃ M : V → Finset V,
      C ⊆ B ∧ IsStarPacking G A C ell M ∧
      (∀ b ∈ C, (M b).card = ell) ∧
      (∀ w ∈ C.biUnion M,
        ((B \ C).filter fun b => G.Adj w b).card ≤ dA) ∧
      (A.Nonempty → C.Nonempty) := by
  classical
  obtain ⟨L,hL,hm⟩ := exists_maximum_star_packing G A B ell
  by_cases hcover : B.biUnion L = A
  · refine ⟨B,L,Finset.Subset.rfl,hL,hL.full_of_cover hsize hcover,?_,?_⟩
    · intro w _; simp
    · intro hAn
      obtain ⟨x,hx⟩ := hAn
      rw [← hcover] at hx
      obtain ⟨b,hb,_⟩ := Finset.mem_biUnion.mp hx
      exact ⟨b,hb⟩
  · have hx : ∃ x ∈ A, x ∉ B.biUnion L := by
      by_contra hn
      push Not at hn
      exact hcover (Finset.Subset.antisymm hL.covered_subset hn)
    obtain ⟨x,hxA,hxn⟩ := hx
    let C := reachableStarCenters G B L x
    let M := fun b => if b ∈ C then L b else ∅
    have hCB : C ⊆ B := reachableStarCenters_subset G B L x
    have hMC : IsStarPacking G A C ell M := hL.restrict_centers (C := C)
    have hu : C.biUnion M = C.biUnion L := restrict_star_union
    refine ⟨C,M,hCB,hMC,?_,?_,?_⟩
    · intro b hb
      have hf := reachableStarCenters_full hL hm hxA hxn b hb
      simpa [M,hb] using hf
    · intro w hw
      rw [hu] at hw
      have hbnd := reachableStarCenters_boundary hL x hw
      obtain ⟨b,_,hwb⟩ := Finset.mem_biUnion.mp hw
      exact hbnd.trans (hA w (hL.2.1 b hwb))
    · intro _
      exact reachableStarCenters_nonempty hL x ((hA x hxA).trans_lt (hdeg.trans_le (hB x hxA)))

end MinorFreeSpanners
