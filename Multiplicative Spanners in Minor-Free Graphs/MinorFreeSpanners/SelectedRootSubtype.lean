import MinorFreeSpanners.SelectedRootPriorLabels

/-! Exact conversion from the selected-family root index to the subtype of
mixed root vertices, retaining the high/weak flag and original labels. -/
namespace MinorFreeSpanners
open Finset
attribute [local instance] Classical.propDecidable

attribute [-instance] instDecidableEqSum in
noncomputable def selectedRootVertex {I : Type*} (P : Finset (Finset I))
    (S : {S // S∈P}) : {r // r∈selectedRoots P} :=
  ⟨Sum.inl S,by classical simp [selectedRoots]⟩

attribute [-instance] instDecidableEqSum in
noncomputable def selectedRootHigh {I : Type*} (P : Finset (Finset I))
    (high : Finset {S // S∈P}) : Finset {r // r∈selectedRoots P} := by
  classical
  exact high.image (selectedRootVertex P)

attribute [-instance] instDecidableEqSum in
 theorem selectedRootHigh_image {I : Type*} (P : Finset (Finset I))
    (high : Finset {S // S∈P}) :
    (selectedRootHigh P high).image Subtype.val=highRootEligible P high := by
  classical
  simp only [selectedRootHigh,highRootEligible,Finset.image_image]
  ext j
  simp [selectedRootVertex]

attribute [-instance] instDecidableEqSum in
 theorem selectedRootWeak_image {I : Type*} (P : Finset (Finset I))
    (high : Finset {S // S∈P}) :
    (Finset.univ\selectedRootHigh P high).image Subtype.val=weakRootPrior P high := by
  classical
  ext j
  constructor
  · intro hj
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hj
    have hp := r.property
    simp only [selectedRoots,Finset.mem_image] at hp
    obtain ⟨S,_,he⟩ := hp
    have hn : S∉high := by
      intro hS
      apply (Finset.mem_sdiff.mp hr).2
      exact Finset.mem_image.mpr ⟨S,hS,Subtype.ext he⟩
    simp only [weakRootPrior,Finset.mem_image]
    exact ⟨S,Finset.mem_sdiff.mpr ⟨mem_univ _,hn⟩,he⟩
  · intro hj
    simp only [weakRootPrior,Finset.mem_image] at hj
    obtain ⟨S,hS,rfl⟩ := hj
    refine Finset.mem_image.mpr ⟨selectedRootVertex P S,Finset.mem_sdiff.mpr ⟨mem_univ _,?_⟩,rfl⟩
    intro hh
    obtain ⟨U,hU,he⟩ := Finset.mem_image.mp hh
    have he' : U=S := Sum.inl.inj (congrArg Subtype.val he)
    exact (Finset.mem_sdiff.mp hS).2 (he' ▸ hU)

end MinorFreeSpanners
