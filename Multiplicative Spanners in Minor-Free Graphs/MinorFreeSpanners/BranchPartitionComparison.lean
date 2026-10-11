import MinorFreeSpanners.FullContractionModel
import MinorFreeSpanners.MinorHostTransport

/-! Exact branch matching transports every actual simple edge into a full
quotient. This lets a constructed contraction be replaced by its canonical
finite star-family quotient without assuming an edge-loss oracle. -/
namespace MinorFreeSpanners
open SimpleGraph
attribute [local instance] Classical.propDecidable
namespace MinorModel
variable {I J V : Type*} [Fintype I] [Fintype J]
variable {F : SimpleGraph I} {Q : SimpleGraph J} {G : SimpleGraph V}

theorem edge_count_le_of_branch_match (M : MinorModel F G) (N : MinorModel Q G)
    (hN : N.IsFull) (hmatch : ∀ i, ∃ j, M.branch i=N.branch j) :
    F.edgeFinset.card ≤ Q.edgeFinset.card := by
  classical
  choose f hf using hmatch
  have hi : Function.Injective f := by
    intro i j he
    obtain ⟨x,hx⟩ := M.nonempty i
    have hj : x ∈ M.branch j := by rw [hf j,← he,← hf i];exact hx
    exact M.branch_unique hx hj
  let g : F →g Q := {
    toFun := f
    map_rel' := by
      intro i j hij
      obtain ⟨x,hx,y,hy,hxy⟩ := M.adjacent i j hij
      exact hN (f i) (f j) (fun he => hij.ne (hi he))
        x (by rwa [← hf i]) y (by rwa [← hf j]) hxy }
  exact hom_edge_count_le g hi

end MinorModel
end MinorFreeSpanners
