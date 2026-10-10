import MinorFreeSpanners.MinimumBadStarFamily
import MinorFreeSpanners.StarCrossingFiber
import MinorFreeSpanners.CommonNeighborIncidences
import MinorFreeSpanners.CrossingSurplusBudget

/-! Actual aggregate ordered crossing surplus, with the real bad-pair score
left visible. Conversion to the full quotient loss and the quantitative
bound on that score are separate remaining arguments. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
variable {V : Type*} [Fintype V]
attribute [local instance] Classical.propDecidable

/-- Real directed same-star collision count at a host vertex. -/
noncomputable def starCollision (G : SimpleGraph V) (L : V → Finset V) (b z : V) : ℕ :=
  (starCrossLeaves G L b z).card*((starCrossLeaves G L b z).card-1)

/-- The literal ordered surplus of crossing fibers between distinct centers. -/
noncomputable def orderedStarSurplus (G : SimpleGraph V) (C : Finset V)
    (L : V → Finset V) : ℕ :=
  ∑ b ∈ C, ∑ c ∈ C, if b≠c then
    (starCrossLeaves G L b c).card+(starCrossLeaves G L c b).card-1 else 0

omit [Fintype V] in
theorem badStarPairCount_eq_sum (G : SimpleGraph V) (C : Finset V) (L : V → Finset V) :
    badStarPairCount G C L = ∑ b ∈ C, ∑ c ∈ C, if IsBadStarPair G L b c then 1 else 0 := by
  classical
  rw [badStarPairCount,Finset.card_eq_sum_ones,Finset.sum_filter]
  exact Finset.sum_product _ _ _

/-- Sum the actual two-direction crossing bound, then enlarge each second
center domain to all host vertices. This retains the actual bad-pair count. -/
theorem orderedStarSurplus_le (G : SimpleGraph V) (C : Finset V) (L : V → Finset V) :
    orderedStarSurplus G C L ≤
      2*(∑ b ∈ C, ∑ z : V, starCollision G L b z)+badStarPairCount G C L := by
  classical
  have hp (b c : V) :
      (if b≠c then (starCrossLeaves G L b c).card+
        (starCrossLeaves G L c b).card-1 else 0) ≤
      starCollision G L b c+starCollision G L c b+
        (if IsBadStarPair G L b c then 1 else 0) := by
    by_cases hbc : b=c
    · simp [hbc]
    · simpa [starCollision,IsBadStarPair,hbc] using crossing_surplus_budget
        (starCrossLeaves G L b c).card (starCrossLeaves G L c b).card
  have hsum := Finset.sum_le_sum (s:=C) (fun b _ =>
    Finset.sum_le_sum (s:=C) (fun c _ => hp b c))
  have hswap : (∑ b ∈ C, ∑ c ∈ C, starCollision G L c b) =
      ∑ b ∈ C, ∑ c ∈ C, starCollision G L b c := Finset.sum_comm
  have hdom : (∑ b ∈ C, ∑ c ∈ C, starCollision G L b c) ≤
      ∑ b ∈ C, ∑ z : V, starCollision G L b z := by
    apply Finset.sum_le_sum
    intro b _
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ C)
  simp_rw [Finset.sum_add_distrib] at hsum
  rw [hswap,← badStarPairCount_eq_sum] at hsum
  exact hsum.trans (by omega)

/-- Mate-free leaf sets and exact leaf cardinalities supply a genuine
aggregate real-number budget, with no numerical incidence oracle. -/
theorem orderedStarSurplus_mateFree (G : SimpleGraph V) (C : Finset V)
    (L : V → Finset V) (ell : ℕ) (q : ℝ)
    (hfull : ∀ b ∈ C, (L b).card=ell)
    (hfree : ∀ b ∈ C, MateFreeOn G q (L b:Set V)) :
    (orderedStarSurplus G C L:ℝ) ≤
      2*(ell*(ell-1):ℕ)*q*C.card+(badStarPairCount G C L:ℝ) := by
  have hbudget : ((∑ b ∈ C, ∑ z : V, starCollision G L b z : ℕ):ℝ) ≤
      (ell*(ell-1):ℕ)*q*C.card := by
    push_cast
    calc
      _ ≤ ∑ b ∈ C, ((ell*(ell-1):ℕ):ℝ)*q := by
        apply Finset.sum_le_sum
        intro b hb
        have hh := MateFreeOn.ordered_collision_budget G (L b) q (hfree b hb)
        rw [hfull b hb] at hh
        simpa only [starCollision,starCrossLeaves,Nat.cast_sum] using hh
      _ = _ := by simp [mul_comm]
  have h := Nat.cast_le (α:=ℝ).mpr (orderedStarSurplus_le G C L)
  push_cast at h hbudget ⊢
  nlinarith

/-- This is the literal parallel-edge suppression cost in one real
selected-star quotient fiber, bounded by actual collision witnesses. -/
theorem IsStarPacking.selected_fiber_surplus_le {G : SimpleGraph V} {A B C : Finset V}
    {ell : ℕ} {L : V → Finset V} (h : IsStarPacking G A C ell L)
    (hG : G.IsBipartiteWith (A:Set V) (B:Set V)) (hCB : C ⊆ B)
    (b c : C) (hbc : b ≠ c) :
    (((quotientCrossEdges G (fullStarLabel C L)).filter fun e =>
      Sym2.map (fullStarLabel C L) e=s(Sum.inl b,Sum.inl c)).card-1) ≤
      starCollision G L b.val c.val+starCollision G L c.val b.val+
        (if IsBadStarPair G L b.val c.val then 1 else 0) := by
  classical
  rw [h.selected_edge_fiber_card hG hCB b c hbc]
  have hn : b.val≠c.val := fun he => hbc (Subtype.ext he)
  simpa [starCollision,IsBadStarPair,hn] using crossing_surplus_budget
    (starCrossLeaves G L b.val c.val).card (starCrossLeaves G L c.val b.val).card

end MinorFreeSpanners
