import MinorFreeSpanners.ActualGroupReindex
import MinorFreeSpanners.PartialResidualOwnership

/-! Expanded roots are indexed by their literal original old-label unions.
The reindexing preserves the actual host carriers, without replacing a mixed
connector by a newly chosen original-label representative. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

attribute [-instance] instDecidableEqSum in
 theorem originalMixedLabels_biUnion {I J : Type*} [DecidableEq J]
    (P : Finset (Finset I)) (R : Finset J) (S : J → Finset (SelectedResidualIndex P)) :
    originalMixedLabels P (R.biUnion S)=R.biUnion (fun j => originalMixedLabels P (S j)) := by
  classical
  ext i
  simp only [originalMixedLabels,Finset.mem_biUnion]
  aesop

namespace ClusterFamily
variable {I J V : Type*} {A G : SimpleGraph V} {w : Sym2 V → ℝ} {D E E' : ℝ}

attribute [-instance] instDecidableEqSum in
 theorem mixed_union_branch_original (C : ClusterFamily (I:=I) A w D) (hA : A≤G)
    (P : Finset (Finset I)) (F : ClusterFamily (I:={S // S∈P}) G w E)
    (hbranch : ∀ S,F.branch S={x | ∃ i∈S.val,x∈C.branch i})
    (S : Finset (SelectedResidualIndex P)) :
    {x | ∃ j∈S,x∈(C.selectedResidual hA P F hbranch).branch j}=
      {x | ∃ i∈originalMixedLabels P S,x∈C.branch i} := by
  classical
  ext x
  constructor
  · rintro ⟨j,hj,hx⟩
    obtain ⟨i,hi,hxi⟩ := (C.mixed_branch_original hA P F hbranch j x).mp hx
    exact ⟨i,Finset.mem_biUnion.mpr ⟨j,hj,hi⟩,hxi⟩
  · rintro ⟨i,hi,hxi⟩
    obtain ⟨j,hj,hi⟩ := Finset.mem_biUnion.mp hi
    exact ⟨j,hj,(C.mixed_branch_original hA P F hbranch j x).mpr ⟨i,hi,hxi⟩⟩

attribute [-instance] instDecidableEqSum in
 theorem expanded_original_groups [Fintype J] (C : ClusterFamily (I:=I) A w D) (hA : A≤G)
    (P : Finset (Finset I)) (F : ClusterFamily (I:={S // S∈P}) G w E)
    (hbranch : ∀ S,F.branch S={x | ∃ i∈S.val,x∈C.branch i})
    (S : J → Finset (SelectedResidualIndex P)) (Fnew : ClusterFamily (I:=J) G w E')
    (hnew : ∀ j,Fnew.branch j={x | ∃ i∈S j,x∈(C.selectedResidual hA P F hbranch).branch i}) :
    let groups := fun j => originalMixedLabels P (S j)
    ∃ e : J ≃ {U // U∈Finset.univ.image groups},
      (∀ j,(e j).val=groups j) ∧
      (∀ U,(Fnew.reindex e.symm).branch U={x | ∃ i∈U.val,x∈C.branch i}) ∧
      (∀ j k,j≠k → Disjoint (groups j) (groups k)) ∧
      (Finset.univ.image groups).biUnion id=originalMixedLabels P (Finset.univ.biUnion S) := by
  classical
  intro groups
  have hb : ∀ j,Fnew.branch j={x | ∃ i∈groups j,x∈C.branch i} := by
    intro j
    rw [hnew j,C.mixed_union_branch_original hA P F hbranch]
  let e := C.originalGroupEquiv Fnew groups hb
  refine ⟨e,fun _ => rfl,C.reindexed_group_branch Fnew groups hb,
    C.original_groups_disjoint Fnew groups hb,?_⟩
  rw [originalMixedLabels_biUnion]
  ext i
  simp only [Finset.mem_biUnion,Finset.mem_image,Finset.mem_univ,true_and]
  aesop

end ClusterFamily
end MinorFreeSpanners
