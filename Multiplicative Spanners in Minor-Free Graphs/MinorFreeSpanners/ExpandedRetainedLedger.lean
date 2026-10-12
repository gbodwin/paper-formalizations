import MinorFreeSpanners.ExpandedResidualLabels
import MinorFreeSpanners.SelectedRootCreditTransfer

/-! Original high/weak bills and all surviving singleton credit are reindexed
exactly. Root metric-plus-future allocations retain their same values. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

attribute [-instance] instDecidableEqSum in
 theorem expanded_root_labels_image {I J : Type*} [Fintype J]
    (P U : Finset (Finset I)) (S : J → Finset (SelectedResidualIndex P))
    (e : J ≃ {g // g∈U}) (he : ∀ j,(e j).val=originalMixedLabels P (S j))
    (R : Finset J) :
    (R.image e).biUnion Subtype.val=originalMixedLabels P (R.biUnion S) := by
  classical
  rw [originalMixedLabels_biUnion]
  ext i
  simp only [Finset.mem_biUnion,Finset.mem_image]
  constructor
  · rintro ⟨g,⟨j,hj,rfl⟩,hi⟩
    exact ⟨j,hj,he j ▸ hi⟩
  · rintro ⟨j,hj,hi⟩
    exact ⟨e j,⟨j,hj,rfl⟩,(he j).symm ▸ hi⟩

 theorem equiv_complement_image {J K : Type*} [Fintype J] [Fintype K] [DecidableEq J] [DecidableEq K]
    (e : J ≃ K) (R : Finset J) : Finset.univ\R.image e=(Finset.univ\R).image e := by
  classical
  ext k
  constructor
  · intro hk
    refine Finset.mem_image.mpr ⟨e.symm k,Finset.mem_sdiff.mpr ⟨mem_univ _,?_⟩,e.apply_symm_apply k⟩
    intro hi
    exact (Finset.mem_sdiff.mp hk).2 (Finset.mem_image.mpr ⟨e.symm k,hi,e.apply_symm_apply k⟩)
  · intro hk
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hk
    refine Finset.mem_sdiff.mpr ⟨mem_univ _,?_⟩
    intro he
    obtain ⟨i,hi,hij⟩ := Finset.mem_image.mp he
    exact (Finset.mem_sdiff.mp hj).2 (e.injective hij ▸ hi)

attribute [-instance] instDecidableEqSum in
 theorem expanded_surviving_credit {I : Type*} [Fintype I]
    (P : Finset (Finset I)) (S : Finset (SelectedResidualIndex P))
    (hroot : selectedRoots P⊆S) (root : {g // g∈P} → ℝ) (credit : I → ℝ) :
    (∑ j∈Finset.univ\S,selectedResidualCredit P root credit j)=
      ∑ i∈Finset.univ\originalMixedLabels P S,credit i := by
  classical
  let f : (j : SelectedResidualIndex P) → j∈Finset.univ\S → I := by
    intro j hj
    cases j with
    | inl g => exact ((Finset.mem_sdiff.mp hj).2 (hroot (by simp [selectedRoots]))).elim
    | inr i => exact i.val
  apply Finset.sum_bij f
  · intro j hj
    cases j with
    | inl g => exact ((Finset.mem_sdiff.mp hj).2 (hroot (by simp [selectedRoots]))).elim
    | inr i =>
      exact Finset.mem_sdiff.mpr ⟨mem_univ _,fun hi =>
        (Finset.mem_sdiff.mp hj).2 ((residual_mem_originalMixedLabels P S i).mp hi)⟩
  · intro j hj k hk he
    cases j with
    | inl g => exact ((Finset.mem_sdiff.mp hj).2 (hroot (by simp [selectedRoots]))).elim
    | inr i =>
      cases k with
      | inl g => exact ((Finset.mem_sdiff.mp hk).2 (hroot (by simp [selectedRoots]))).elim
      | inr j => exact congrArg Sum.inr (Subtype.ext he)
  · intro i hi
    have hn : i∉P.biUnion id := fun hh =>
      (Finset.mem_sdiff.mp hi).2 (old_selected_subset_expanded P S hroot hh)
    refine ⟨Sum.inr ⟨i,hn⟩,Finset.mem_sdiff.mpr ⟨mem_univ _,?_⟩,rfl⟩
    exact fun hh => (Finset.mem_sdiff.mp hi).2 ((residual_mem_originalMixedLabels P S ⟨i,hn⟩).mpr hh)
  · intro j hj
    cases j with
    | inl g => exact ((Finset.mem_sdiff.mp hj).2 (hroot (by simp [selectedRoots]))).elim
    | inr i => rfl

namespace ClusterFamily
variable {I J V : Type*} [Fintype I] [Fintype J] [Fintype V]
variable {A B : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}

attribute [-instance] instDecidableEqSum in
 theorem reindex_expanded_paid_ledger [DecidableEq J] (C : ClusterFamily (I:=I) A w D)
    (P U : Finset (Finset I)) (S : J → Finset (SelectedResidualIndex P))
    (hroot : selectedRoots P⊆Finset.univ.biUnion S)
    (hU : U.biUnion id=originalMixedLabels P (Finset.univ.biUnion S))
    (e : J ≃ {g // g∈U}) (he : ∀ j,(e j).val=originalMixedLabels P (S j))
    (high : Finset J) (oldRoot : {g // g∈P} → ℝ) (credit : I → ℝ)
    (cost : J → ℝ) (budget : ℝ)
    (hpaid :
      (∑ f∈C.touchingEdges B (originalMixedLabels P ((Finset.univ\high).biUnion S)),w f)+
      (∑ f∈C.markedEdges B (originalMixedLabels P (high.biUnion S)),w f)+
      (∑ j,cost j)+(∑ i∈Finset.univ\Finset.univ.biUnion S,selectedResidualCredit P oldRoot credit i)≤budget) :
    (∑ f∈C.touchingEdges B ((Finset.univ\high.image e).biUnion Subtype.val),w f)+
    (∑ f∈C.markedEdges B ((high.image e).biUnion Subtype.val),w f)+
    (∑ i,selectedResidualCredit U (fun g => cost (e.symm g)) credit i)≤budget := by
  classical
  rw [equiv_complement_image e high,expanded_root_labels_image P U S e he,
    expanded_root_labels_image P U S e he,selectedResidualCredit_sum]
  have hcost : (∑ g,cost (e.symm g))=∑ j,cost j := e.symm.sum_comp cost
  rw [hcost,hU]
  rw [expanded_surviving_credit P _ hroot oldRoot credit] at hpaid
  linarith

end ClusterFamily

end MinorFreeSpanners
