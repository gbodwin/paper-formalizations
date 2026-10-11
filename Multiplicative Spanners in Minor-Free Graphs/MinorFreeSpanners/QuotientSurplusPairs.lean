import MinorFreeSpanners.SimpleQuotientCount

/-! A conservative ordered-pair upper budget for the actual unordered
simple-quotient fiber losses. No choice of edge orientation is assumed. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V I : Type*} [Fintype V] [Fintype I]

omit [Fintype V] in
/-- Every actual unordered edge has an ordered representative. Summing a
nonnegative natural cost over all ordered pairs therefore dominates its
sum on the real edge set, even with loops and reversals in the larger domain. -/
theorem edge_cost_le_ordered_pairs (G : SimpleGraph I) [Fintype G.edgeSet]
    (cost : Sym2 I → ℕ) :
    ∑ e ∈ G.edgeFinset, cost e ≤ ∑ i : I, ∑ j : I, cost s(i,j) := by
  classical
  have hsub : G.edgeFinset ⊆ (Finset.univ : Finset (I×I)).image (fun p => s(p.1,p.2)) := by
    intro e _
    obtain ⟨p,hp⟩ := Sym2.mk_surjective e
    exact Finset.mem_image.mpr ⟨p,Finset.mem_univ _,hp⟩
  calc
    _ ≤ ∑ e ∈ (Finset.univ : Finset (I×I)).image (fun p => s(p.1,p.2)), cost e :=
      Finset.sum_le_sum_of_subset hsub
    _ ≤ ∑ p : I×I, cost s(p.1,p.2) :=
      Finset.sum_image_le_of_nonneg (fun _ _ => Nat.zero_le _)
    _ = _ := Fintype.sum_prod_type _

/-- Literal full quotient surplus is bounded through actual crossing
fibers indexed by all ordered quotient-vertex pairs. -/
theorem quotient_surplus_le_ordered_pairs (G : SimpleGraph V) (f : V → I) :
    (∑ e ∈ (G.map f).edgeFinset,
      (((quotientCrossEdges G f).filter fun a => Sym2.map f a=e).card-1)) ≤
      ∑ i : I, ∑ j : I,
        (((quotientCrossEdges G f).filter fun a => Sym2.map f a=s(i,j)).card-1) :=
  edge_cost_le_ordered_pairs (G.map f) _

omit [Fintype I] in
/-- A true crossing edge never maps to a loop. -/
theorem quotient_diagonal_fiber_empty (G : SimpleGraph V) (f : V → I) (i : I) :
    ((quotientCrossEdges G f).filter fun a => Sym2.map f a=s(i,i)) = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨he,hi⟩ := Finset.mem_filter.mp he
  have hn := (Finset.mem_filter.mp he).2
  rw [hi] at hn
  exact hn (by simp)

end MinorFreeSpanners
