import MinorFreeSpanners.MixedPriorEdgeTransport
import MinorFreeSpanners.MixedSmallAbsorptionPhase

/-! Weak selected roots give the actual prior-paid mixed labels. Disjointness
of the original selected groups identifies the remaining selected labels with
exactly the high-degree groups, so the earlier bill has the required identity. -/
namespace MinorFreeSpanners
open Finset
attribute [local instance] Classical.propDecidable
variable {I : Type*}

noncomputable def weakRootPrior (P : Finset (Finset I))
    (high : Finset {S // S∈P}) : Finset (SelectedResidualIndex P) := by
  classical
  exact (Finset.univ\high).image Sum.inl

noncomputable def highRootEligible (P : Finset (Finset I))
    (high : Finset {S // S∈P}) : Finset (SelectedResidualIndex P) := by
  classical
  exact high.image Sum.inl

 theorem selected_roots_prior_or_eligible (P : Finset (Finset I))
    (high : Finset {S // S∈P}) :
    selectedRoots P\highRootEligible P high=weakRootPrior P high := by
  classical
  ext j
  cases j <;> simp [selectedRoots,highRootEligible,weakRootPrior]

 theorem original_weakRootPrior (P : Finset (Finset I))
    (high : Finset {S // S∈P}) :
    originalMixedLabels P (weakRootPrior P high)=(Finset.univ\high).biUnion Subtype.val := by
  classical
  ext i
  simp only [originalMixedLabels,weakRootPrior,Finset.mem_biUnion,Finset.mem_image]
  constructor
  · rintro ⟨_,⟨S,hS,rfl⟩,hi⟩
    exact ⟨S,hS,hi⟩
  · rintro ⟨S,hS,hi⟩
    exact ⟨Sum.inl S,⟨S,hS,rfl⟩,hi⟩

 theorem selected_group_union (P : Finset (Finset I)) :
    (Finset.univ : Finset {S // S∈P}).biUnion Subtype.val=P.biUnion id := by
  classical
  ext i
  simp

 theorem selected_high_labels (P : Finset (Finset I))
    (hP : ∀ S U,S∈P → U∈P → S≠U → Disjoint S U)
    (high : Finset {S // S∈P}) :
    P.biUnion id\originalMixedLabels P (weakRootPrior P high)=high.biUnion Subtype.val := by
  classical
  rw [original_weakRootPrior,←selected_group_union]
  ext i
  constructor
  · intro hi
    obtain ⟨hi,hn⟩ := Finset.mem_sdiff.mp hi
    obtain ⟨S,_,hi⟩ := Finset.mem_biUnion.mp hi
    have hh : S∈high := by
      by_contra hh
      exact hn (Finset.mem_biUnion.mpr ⟨S,Finset.mem_sdiff.mpr ⟨by simp,hh⟩,hi⟩)
    exact Finset.mem_biUnion.mpr ⟨S,hh,hi⟩
  · intro hi
    obtain ⟨S,hS,hi⟩ := Finset.mem_biUnion.mp hi
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨S,by simp,hi⟩,?_⟩
    intro hn
    obtain ⟨U,hU,hu⟩ := Finset.mem_biUnion.mp hn
    have hne : S.val≠U.val := fun h =>
      (Finset.mem_sdiff.mp hU).2 ((Subtype.ext h : S=U) ▸ hS)
    exact Finset.disjoint_left.mp (hP S.val U.val S.property U.property hne) hi hu

end MinorFreeSpanners
