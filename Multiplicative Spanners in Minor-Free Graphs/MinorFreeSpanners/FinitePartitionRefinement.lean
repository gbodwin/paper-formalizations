import MinorFreeSpanners.ResidualOwnershipPartition

/-! Disjoint local refinements of disjoint actual carriers produce a global
partition. This supplies the coverage and single-use bookkeeping needed to
combine independently chosen rooted path assemblies. -/
namespace MinorFreeSpanners
open Finset
attribute [local instance] Classical.propDecidable

 theorem finite_partition_refinement {I J : Type*} [Fintype J]
    (carrier : J → Finset I) (P : J → Finset (Finset I))
    (houter : ∀ i j,i≠j → Disjoint (carrier i) (carrier j))
    (hcover : ∀ j,(P j).biUnion id=carrier j)
    (hne : ∀ j,∀ S∈P j,S.Nonempty)
    (hdis : ∀ j,∀ S∈P j,∀ T∈P j,S≠T → Disjoint S T) :
    let out := Finset.univ.biUnion P
    (∀ S∈out,S.Nonempty) ∧
    (∀ S∈out,∀ T∈out,S≠T → Disjoint S T) ∧
    out.biUnion id=Finset.univ.biUnion carrier ∧
    (∀ i j,i≠j → Disjoint (P i) (P j)) := by
  classical
  have hsub : ∀ j,∀ S∈P j,S⊆carrier j := by
    intro j S hS x hx
    rw [←hcover j]
    exact Finset.mem_biUnion.mpr ⟨S,hS,hx⟩
  refine ⟨?_,?_,?_,?_⟩
  · intro S hS
    obtain ⟨j,_,hS⟩ := Finset.mem_biUnion.mp hS
    exact hne j S hS
  · intro S hS T hT hST
    obtain ⟨i,_,hS⟩ := Finset.mem_biUnion.mp hS
    obtain ⟨j,_,hT⟩ := Finset.mem_biUnion.mp hT
    by_cases hij : i=j
    · subst j;exact hdis i S hS T hT hST
    · exact (houter i j hij).mono (hsub i S hS) (hsub j T hT)
  · ext x
    simp only [Finset.mem_biUnion,Finset.mem_univ,true_and,id_eq]
    constructor
    · rintro ⟨S,⟨j,hS⟩,hx⟩
      exact ⟨j,hsub j S hS hx⟩
    · rintro ⟨j,hx⟩
      rw [←hcover j] at hx
      obtain ⟨S,hS,hx⟩ := Finset.mem_biUnion.mp hx
      exact ⟨S,⟨j,hS⟩,hx⟩
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro S hS hT
    obtain ⟨x,hx⟩ := hne i S hS
    exact Finset.disjoint_left.mp (houter i j hij) (hsub i S hS hx) (hsub j S hT hx)

end MinorFreeSpanners
