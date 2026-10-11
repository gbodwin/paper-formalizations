import MinorFreeSpanners.BranchPartitionComparison

/-! Splitting actual branch sets cannot reduce the full simple quotient's
edge count. Every old crossing edge is realized by a new crossing edge, and
its unordered old endpoint pair is recovered by the proved refinement map. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
namespace MinorModel
variable {I J V : Type*} [Fintype I] [Fintype J]
variable {F : SimpleGraph I} {Q : SimpleGraph J} {G : SimpleGraph V}

theorem edge_count_le_of_branch_refinement (M : MinorModel F G) (N : MinorModel Q G)
    (hcover : N.Covers) (hfull : N.IsFull)
    (hrefine : ∀ j, ∃ i, N.branch j ⊆ M.branch i) :
    F.edgeFinset.card ≤ Q.edgeFinset.card := by
  classical
  choose f hf using hrefine
  have label : ∀ j x, x ∈ N.branch j → ∀ i, x ∈ M.branch i → f j=i := by
    intro j x hx i hi
    exact M.branch_unique (hf j hx) hi
  have hsub : F.edgeFinset ⊆ Q.edgeFinset.image (Sym2.map f) := by
    intro e he
    induction e using Sym2.inductionOn with
    | hf a b =>
      have hab : F.Adj a b := by simpa using he
      obtain ⟨x,hx,y,hy,hxy⟩ := M.adjacent a b hab
      obtain ⟨j,hj⟩ := hcover x
      obtain ⟨l,hl⟩ := hcover y
      have hja := label j x hj a hx
      have hlb := label l y hl b hy
      have hjl : j ≠ l := by
        intro e
        exact hab.ne (hja.symm.trans ((congrArg f e).trans hlb))
      have hadj := hfull j l hjl x hj y hl hxy
      refine Finset.mem_image.mpr ⟨s(j,l),by simpa using hadj,?_⟩
      simp only [Sym2.map_mk,hja,hlb]
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le)

end MinorModel
end MinorFreeSpanners
