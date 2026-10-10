import MinorFreeSpanners.RobustCommonNeighbors

/-! Actual degree loss on one side of a separator. This lemma takes a
separator side explicitly; existence of a suitable side is a later step. -/
namespace MinorFreeSpanners
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

theorem degree_induce_add_separator (G : SimpleGraph V) (A S : Finset V)
    (horizon : ∀ x ∈ A, ∀ y, G.Adj x y → y ∈ A ∨ y ∈ S)
    (x : A) : G.degree x.val ≤ (G.induce (A:Set V)).degree x+S.card := by
  classical
  let H := G.induce (A:Set V)
  let f : G.neighborSet x.val → (H.neighborSet x) ⊕ S := fun y =>
    if hy : y.val ∈ A then Sum.inl ⟨⟨y.val,hy⟩,y.property⟩
    else Sum.inr ⟨y.val,(horizon x.val x.property y.val y.property).resolve_left hy⟩
  let g : (H.neighborSet x) ⊕ S → V := Sum.elim (fun z => z.val.val) Subtype.val
  have hgf : ∀ y, g (f y) = y.val := by
    intro y
    dsimp [f]
    split_ifs <;> rfl
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext ((hgf a).symm.trans ((congrArg g hab).trans (hgf b)))
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_sum,Fintype.card_coe,card_neighborSet_eq_degree] using hc

/-- For a supplied small separator side, the source's degree arithmetic
produces literal robustness under every smaller vertex deletion. -/
theorem small_separator_side_robust (G : SimpleGraph V) (A S : Finset V) (D : ℕ)
    (hdegree : ∀ x ∈ A, 6*D ≤ G.degree x)
    (hA : A.card ≤ 6*D) (hS : S.card ≤ 2*D)
    (horizon : ∀ x ∈ A, ∀ y, G.Adj x y → y ∈ A ∨ y ∈ S) :
    (∀ x : A, 4*D ≤ (G.induce (A:Set V)).degree x) ∧
      DeletionConnected (G.induce (A:Set V)) (2*D) := by
  classical
  have hmin : ∀ x : A, 4*D ≤ (G.induce (A:Set V)).degree x := by
    intro x
    have hg := hdegree x.val x.property
    have hc := degree_induce_add_separator G A S horizon x
    omega
  refine ⟨hmin,deletionConnected_of_degree _ (2*D) (4*D) hmin ?_⟩
  simpa using (show A.card+2*D ≤ 2*(4*D) by omega)

end MinorFreeSpanners
