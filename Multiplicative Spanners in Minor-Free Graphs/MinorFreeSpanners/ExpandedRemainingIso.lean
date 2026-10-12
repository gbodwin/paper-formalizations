import MinorFreeSpanners.ExpandedResidualLabels
import MinorFreeSpanners.SelectedResidualGraphIso

/-! After whole-component absorption, the remaining old mixed singletons and
the new mixed residual vertices are the same original labels. Their induced
graphs and effective masses agree exactly through the common original forest. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

attribute [-instance] instDecidableEqSum in
noncomputable def expandedRemainingEquiv {I : Type*} [Fintype I]
    (P U : Finset (Finset I)) (W : Finset (SelectedResidualIndex P))
    (hroot : selectedRoots P⊆W) (hU : U.biUnion id=originalMixedLabels P W) :
    {i : SelectedResidualIndex P // i∈(Finset.univ\W : Finset _)} ≃
      {j : SelectedResidualIndex U // j∈(Finset.univ\selectedRoots U : Finset _)} where
  toFun := by
    rintro ⟨i,hi⟩
    cases i with
    | inl g => exact ((Finset.mem_sdiff.mp hi).2 (hroot (by simp [selectedRoots]))).elim
    | inr i =>
      have hn : i.val∉U.biUnion id := fun h => (Finset.mem_sdiff.mp hi).2
        ((residual_mem_originalMixedLabels P W i).mp ((Finset.ext_iff.mp hU i.val).mp h))
      exact ⟨Sum.inr ⟨i.val,hn⟩,by simp [selectedRoots]⟩
  invFun := by
    rintro ⟨j,hj⟩
    cases j with
    | inl g => exact ((Finset.mem_sdiff.mp hj).2 (by simp [selectedRoots])).elim
    | inr j =>
      have hn : j.val∉originalMixedLabels P W := fun h =>
        j.property ((Finset.ext_iff.mp hU j.val).mpr h)
      let i := expandedOldResidual P W hroot ⟨j.val,hn⟩
      exact ⟨Sum.inr i,Finset.mem_sdiff.mpr ⟨mem_univ _,expandedOldResidual_outside P W hroot _⟩⟩
  left_inv := by
    rintro ⟨i,hi⟩
    cases i with
    | inl g => exact ((Finset.mem_sdiff.mp hi).2 (hroot (by simp [selectedRoots]))).elim
    | inr i => rfl
  right_inv := by
    rintro ⟨j,hj⟩
    cases j with
    | inl g => exact ((Finset.mem_sdiff.mp hj).2 (by simp [selectedRoots])).elim
    | inr j => rfl

attribute [-instance] instDecidableEqSum in
noncomputable def expandedRemainingIso {I : Type*} [Fintype I]
    (P U : Finset (Finset I)) (W : Finset (SelectedResidualIndex P))
    (hroot : selectedRoots P⊆W) (hU : U.biUnion id=originalMixedLabels P W)
    (H : SimpleGraph (SelectedResidualIndex P)) (K : SimpleGraph (SelectedResidualIndex U))
    (T : SimpleGraph I)
    (hH : ∀ i j : {i // i∉P.biUnion id},H.Adj (Sum.inr i) (Sum.inr j) ↔ T.Adj i.val j.val)
    (hK : ∀ i j : {i // i∉U.biUnion id},K.Adj (Sum.inr i) (Sum.inr j) ↔ T.Adj i.val j.val) :
    H.induce ((Finset.univ\W : Finset _):Set _) ≃g
      K.induce ((Finset.univ\selectedRoots U : Finset _):Set _) where
  toEquiv := expandedRemainingEquiv P U W hroot hU
  map_rel_iff' := by
    rintro ⟨i,hi⟩ ⟨j,hj⟩
    cases i with
    | inl g => exact ((Finset.mem_sdiff.mp hi).2 (hroot (by simp [selectedRoots]))).elim
    | inr i =>
      cases j with
      | inl g => exact ((Finset.mem_sdiff.mp hj).2 (hroot (by simp [selectedRoots]))).elim
      | inr j => exact (hK _ _).trans (hH i j).symm

attribute [-instance] instDecidableEqSum in
 theorem expandedRemainingIso_mass {I : Type*} [Fintype I]
    (P U : Finset (Finset I)) (W : Finset (SelectedResidualIndex P))
    (hroot : selectedRoots P⊆W) (hU : U.biUnion id=originalMixedLabels P W)
    (H : SimpleGraph (SelectedResidualIndex P)) (K : SimpleGraph (SelectedResidualIndex U))
    (T : SimpleGraph I)
    (hH : ∀ i j : {i // i∉P.biUnion id},H.Adj (Sum.inr i) (Sum.inr j) ↔ T.Adj i.val j.val)
    (hK : ∀ i j : {i // i∉U.biUnion id},K.Adj (Sum.inr i) (Sum.inr j) ↔ T.Adj i.val j.val)
    (d : I → ℝ) (oldRadius : {g // g∈P} → ℝ) (newRadius : {g // g∈U} → ℝ)
    (i : {i : SelectedResidualIndex P // i∈(Finset.univ\W : Finset _)}) :
    mixedEffectiveDiameter d newRadius ((expandedRemainingIso P U W hroot hU H K T hH hK) i).val=
      mixedEffectiveDiameter d oldRadius i.val := by
  rcases i with ⟨i,hi⟩
  cases i with
  | inl g => exact ((Finset.mem_sdiff.mp hi).2 (hroot (by simp [selectedRoots]))).elim
  | inr i => rfl

end MinorFreeSpanners
