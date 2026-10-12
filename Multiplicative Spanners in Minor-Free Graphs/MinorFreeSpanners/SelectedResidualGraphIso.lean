import MinorFreeSpanners.SelectedResidualDegree

/-! The two literal residual induced graphs are isomorphic via the actual
singleton labels. This transport never maps a selected root to an old residual. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {I : Type*}

noncomputable def selectedResidualVertexEquiv (P : Finset (Finset I)) :
    {j : SelectedResidualIndex P // j∉selectedRoots P} ≃ {i // i∉P.biUnion id} where
  toFun := by
    rintro ⟨j,hj⟩
    cases j with
    | inl S => exact (hj (by simp [selectedRoots])).elim
    | inr i => exact i
  invFun i := ⟨Sum.inr i,by simp [selectedRoots]⟩
  left_inv := by
    rintro ⟨j,hj⟩
    cases j with
    | inl S => exact (hj (by simp [selectedRoots])).elim
    | inr i => rfl
  right_inv := fun _ => rfl

noncomputable def selectedResidualGraphIso (P : Finset (Finset I))
    (K : SimpleGraph (SelectedResidualIndex P)) (H : SimpleGraph I)
    (hres : ∀ i j : {i // i∉P.biUnion id},K.Adj (Sum.inr i) (Sum.inr j) ↔ H.Adj i.val j.val) :
    K.induce {j | j∉selectedRoots P} ≃g H.induce {i | i∉P.biUnion id} where
  toEquiv := selectedResidualVertexEquiv P
  map_rel_iff' := by
    rintro ⟨i,hi⟩ ⟨j,hj⟩
    cases i with
    | inl S => exact (hi (by simp [selectedRoots])).elim
    | inr i =>
      cases j with
      | inl S => exact (hj (by simp [selectedRoots])).elim
      | inr j => exact (hres i j).symm

end MinorFreeSpanners
