import MinorFreeSpanners.FullContractionModel
import MinorFreeSpanners.EdgeContractionCount

/-! Merge exactly two adjacent actual branches. The new width is their
sum, while every other branch remains literally unchanged. This avoids the
loose factor-two bound from arbitrary bounded-minor composition. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
namespace MinorModel
variable {I V : Type*} {F : SimpleGraph I} {G : SimpleGraph V}

noncomputable def mergeEdge (M : MinorModel F G) {u v : I} (huv : F.Adj u v) :
    MinorModel (contractEdge F u v) G := (contractEdgeModel F u v huv).comp M

theorem mergeEdge_branch_center (M : MinorModel F G) {u v : I} (huv : F.Adj u v) :
    (M.mergeEdge huv).branch ⟨u,huv.ne⟩=M.branch u ∪ M.branch v := by
  ext x
  simp [mergeEdge,MinorModel.comp,contractEdgeModel]

theorem mergeEdge_branch_other (M : MinorModel F G) {u v : I} (huv : F.Adj u v)
    (i : {x : I // x ≠ v}) (hi : i.val ≠ u) :
    (M.mergeEdge huv).branch i=M.branch i.val := by
  ext x
  simp [mergeEdge,MinorModel.comp,contractEdgeModel,hi]

theorem mergeEdge_covers (M : MinorModel F G) {u v : I} (huv : F.Adj u v)
    (hM : M.Covers) : (M.mergeEdge huv).Covers :=
  Covers.comp _ _ (contractEdgeModel_covers F huv) hM

theorem mergeEdge_full (M : MinorModel F G) {u v : I} (huv : F.Adj u v)
    (hM : M.IsFull) : (M.mergeEdge huv).IsFull :=
  IsFull.comp _ _ (contractEdgeModel_full F huv) hM

theorem mergeEdge_center_card [Fintype V] (M : MinorModel F G)
    {u v : I} (huv : F.Adj u v) :
    ((M.mergeEdge huv).branch ⟨u,huv.ne⟩).toFinset.card=
      (M.branch u).toFinset.card+(M.branch v).toFinset.card := by
  classical
  rw [M.mergeEdge_branch_center huv,Set.toFinset_union]
  apply Finset.card_union_of_disjoint
  exact Set.disjoint_toFinset.mpr (M.disjoint u v huv.ne)

/-- Only the sum of the merged branch sizes controls the new width. -/
theorem mergeEdge_bounded [Fintype V] (M : MinorModel F G)
    {u v : I} (huv : F.Adj u v) (k : ℕ) (hM : M.IsBounded k)
    (hsize : (M.branch u).toFinset.card+(M.branch v).toFinset.card ≤ k) :
    (M.mergeEdge huv).IsBounded k := by
  intro i
  by_cases hi : i.val=u
  · have he : i=⟨u,huv.ne⟩ := Subtype.ext hi
    rw [he,M.mergeEdge_center_card huv]
    exact hsize
  · rw [M.mergeEdge_branch_other huv i hi]
    exact hM i.val

/-- Absorbing an actual singleton increases the selected branch by one. -/
theorem mergeEdge_singleton_card [Fintype V] (M : MinorModel F G)
    {u v : I} (huv : F.Adj u v) {x : V} (hx : M.branch v={x}) :
    ((M.mergeEdge huv).branch ⟨u,huv.ne⟩).toFinset.card=
      (M.branch u).toFinset.card+1 := by
  classical
  rw [M.mergeEdge_center_card huv,hx]
  simp

end MinorModel
end MinorFreeSpanners
