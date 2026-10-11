import MinorFreeSpanners.FullBranchFiber
import MinorFreeSpanners.DirectedCrossingBudget

/-! Real singleton-branch fibers have no uncharged parallel-edge loss.
A selected/residual fiber is charged to the actual directed leaf collisions. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

/-- Two residual branches are singletons, so at most one original simple
edge can lie between them. -/
theorem residual_branch_fiber_card_le_one (G : SimpleGraph V) (C : Finset V)
    (L : V → Finset V) (x y : starResidual C L) :
    (branchBetweenEdges G C L (.inr x) (.inr y)).card ≤ 1 := by
  classical
  calc
    _ ≤ ((((fullStarBranch C L (.inr x)).product (fullStarBranch C L (.inr y))).filter
        fun p => G.Adj p.1 p.2)).card := Finset.card_image_le
    _ ≤ ((fullStarBranch C L (.inr x)).product (fullStarBranch C L (.inr y))).card :=
      Finset.card_filter_le _ _
    _ = 1 := by simp [fullStarBranch]

/-- Edges to a residual vertex are exactly the adjacent vertices of the
selected branch, with no duplicate unordered edge representations. -/
theorem selected_residual_branch_edges (G : SimpleGraph V) (C : Finset V)
    (L : V → Finset V) (b : C) (z : starResidual C L) :
    branchBetweenEdges G C L (.inl b) (.inr z) =
      ((insert b.val (L b.val)).filter fun x => G.Adj x z.val).image fun x => s(x,z.val) := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨⟨x,y⟩,hxy,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hm,hadj⟩ := Finset.mem_filter.mp hxy
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hm
    have hyz : y=z.val := by simpa only [fullStarBranch,Finset.mem_singleton] using hy
    subst y
    exact Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨hx,hadj⟩,rfl⟩
  · intro he
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hx,hadj⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_image.mpr ⟨(x,z.val),Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hx,by simp [fullStarBranch]⟩,hadj⟩,rfl⟩

/-- In the actual bipartite graph, a residual vertex adjacent to the
center cannot also be adjacent to a leaf. Otherwise the whole fiber is
exactly the crossing-leaf set, whose excess is bounded by its collisions. -/
theorem IsStarPacking.selected_residual_fiber_surplus {G : SimpleGraph V}
    {A B C : Finset V} {ell : ℕ} {L : V → Finset V}
    (h : IsStarPacking G A C ell L)
    (hG : G.IsBipartiteWith (A:Set V) (B:Set V)) (hCB : C ⊆ B)
    (b : C) (z : starResidual C L) :
    (branchBetweenEdges G C L (.inl b) (.inr z)).card-1 ≤
      starCollision G L b.val z.val := by
  classical
  rw [selected_residual_branch_edges]
  have hi : Function.Injective (fun x : V => s(x,z.val)) := by
    intro x y he
    rcases Sym2.eq_iff.mp he with ⟨he,_⟩ | ⟨hx,hy⟩
    · exact he
    · exact hx.trans hy
  rw [Finset.card_image_of_injective _ hi]
  by_cases hadj : G.Adj b.val z.val
  · have hza := hG.symm.mem_of_mem_adj (hCB b.property) hadj
    have hnone : (L b.val).filter (fun x => G.Adj x z.val) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨hx,hxz⟩ := Finset.mem_filter.mp hx
      exact Set.disjoint_left.mp hG.disjoint hza
        (hG.mem_of_mem_adj (h.2.1 b.val hx) hxz)
    simp [Finset.filter_insert,hadj,hnone]
  · have hp : ((insert b.val (L b.val)).filter fun x => G.Adj x z.val) =
        starCrossLeaves G L b.val z.val := by simp [Finset.filter_insert,hadj,starCrossLeaves]
    rw [hp]
    unfold starCollision
    by_cases hz : (starCrossLeaves G L b.val z.val).card=0
    · simp [hz]
    · have hpos : 1 ≤ (starCrossLeaves G L b.val z.val).card := by omega
      simpa using Nat.mul_le_mul_right ((starCrossLeaves G L b.val z.val).card-1) hpos

end MinorFreeSpanners
