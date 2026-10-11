import MinorFreeSpanners.GeneralStarForest
import MinorFreeSpanners.BranchRefinementCount

/-! Removing selected stars leaves an actual full quotient with at least as
many edges. The old star labels are replaced by original singleton vertices;
no host edge or vertex is deleted to obtain this refinement. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem IsGeneralStarForest.restrict {G : SimpleGraph V} {k : ℕ}
    {C C' : Finset V} {L : V → Finset V} (h : IsGeneralStarForest G k C L)
    (hsub : C' ⊆ C) : IsGeneralStarForest G k C' L :=
  ⟨fun c hc => h.1 c (hsub hc),fun c hc => h.2.1 c (hsub hc),
    fun c hc b hb hcb => h.2.2 c (hsub hc) b (hsub hb) hcb⟩

theorem IsGeneralStarForest.subfamily_edges {G : SimpleGraph V} {k : ℕ}
    {C C' : Finset V} {L : V → Finset V} (h : IsGeneralStarForest G k C L)
    (hsub : C' ⊆ C) :
    (fullStarContraction G C L).edgeFinset.card ≤ (fullStarContraction G C' L).edgeFinset.card := by
  let h' := h.restrict hsub
  apply h.fullMinorModel.edge_count_le_of_branch_refinement h'.fullMinorModel
    h'.fullMinorModel_covers h'.fullMinorModel_full
  intro j
  cases j with
  | inl c => exact ⟨.inl ⟨c.val,hsub c.property⟩,fun _ hx => hx⟩
  | inr x =>
    obtain ⟨i,hi⟩ := h.fullMinorModel_covers x.val
    refine ⟨i,?_⟩
    intro y hy
    have hy' : y=x.val := by simpa [IsGeneralStarForest.fullMinorModel,fullStarBranch] using hy
    simpa only [hy'] using hi

end MinorFreeSpanners
