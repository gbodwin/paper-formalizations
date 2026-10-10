import MinorFreeSpanners.StarCrossingPairs

/-! Internally choose a true minimum-bad-pair star family on a fixed set of
centers and covered leaves. The later swap/counting theorem is not assumed. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Ordered bad center pairs. Distinctness is part of IsBadStarPair. -/
noncomputable def badStarPairCount (G : SimpleGraph V) (C : Finset V)
    (L : V → Finset V) : ℕ :=
  ((C.product C).filter fun p => IsBadStarPair G L p.1 p.2).card

/-- A minimizing actual assignment exists, preserving exactly the old
covered leaves, all fullness and original-host mate-free branches. The
minimum is over actual valid assignments, not an assumed oracle. -/
theorem exists_minimum_bad_star_family (G : SimpleGraph V) (A C : Finset V)
    (ell : ℕ) (q : ℝ) (L : V → Finset V)
    (hL : IsStarPacking G A C ell L) (hfull : ∀ b ∈ C, (L b).card = ell)
    (hfree : ∀ b ∈ C, MateFreeOn G q (insert b (L b:Set V))) :
    ∃ M : V → Finset V,
      IsStarPacking G A C ell M ∧
      (∀ b ∈ C, (M b).card = ell) ∧
      (∀ b ∈ C, MateFreeOn G q (insert b (M b:Set V))) ∧
      C.biUnion M = C.biUnion L ∧
      ∀ N : V → Finset V,
        IsStarPacking G A C ell N →
        (∀ b ∈ C, (N b).card = ell) →
        (∀ b ∈ C, MateFreeOn G q (insert b (N b:Set V))) →
        C.biUnion N = C.biUnion L →
        badStarPairCount G C M ≤ badStarPairCount G C N := by
  classical
  let P := fun M : V → Finset V =>
    IsStarPacking G A C ell M ∧
      (∀ b ∈ C, (M b).card = ell) ∧
      (∀ b ∈ C, MateFreeOn G q (insert b (M b:Set V))) ∧
      C.biUnion M = C.biUnion L
  have hex : ∃ n : ℕ, ∃ M, P M ∧ badStarPairCount G C M = n :=
    ⟨badStarPairCount G C L,L,⟨hL,hfull,hfree,rfl⟩,rfl⟩
  obtain ⟨M,hM,hmin⟩ := Nat.find_spec hex
  refine ⟨M,hM.1,hM.2.1,hM.2.2.1,hM.2.2.2,?_⟩
  intro N hN hf hn hc
  rw [hmin]
  exact Nat.find_min' hex ⟨N,⟨hN,hf,hn,hc⟩,rfl⟩

end MinorFreeSpanners
