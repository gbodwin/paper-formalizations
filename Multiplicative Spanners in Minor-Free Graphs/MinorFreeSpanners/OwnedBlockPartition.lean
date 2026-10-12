import MinorFreeSpanners.FinitePartitionRefinement

/-! Assigning actual disjoint blocks to existing disjoint root carriers gives
a disjoint complete simultaneous absorption. Root carriers may themselves be
previously grown blocks; every original old label is retained exactly once. -/
namespace MinorFreeSpanners
open Finset
attribute [local instance] Classical.propDecidable

noncomputable def assignedBlockUnion {I J : Type*} (P : Finset (Finset I))
    (owner : {S // S∈P} → J) (j : J) : Finset I := by
  classical
  exact (Finset.univ.filter (fun S : {S // S∈P} => owner S=j)).biUnion Subtype.val

 theorem mem_assignedBlockUnion {I J : Type*} (P : Finset (Finset I))
    (owner : {S // S∈P} → J) (j : J) (x : I) :
    x∈assignedBlockUnion P owner j ↔ ∃ S : {S // S∈P},owner S=j ∧ x∈S.val := by
  classical
  simp [assignedBlockUnion]

 theorem owned_block_partition {I J : Type*} [Fintype J]
    (P : Finset (Finset I)) (root : J → Finset I) (owner : {S // S∈P} → J)
    (hne : ∀ j,(root j).Nonempty)
    (hroots : ∀ i j,i≠j → Disjoint (root i) (root j))
    (hrootP : ∀ j,Disjoint (root j) (P.biUnion id))
    (hP : ∀ S∈P,∀ T∈P,S≠T → Disjoint S T) :
    let filled := fun j => root j∪assignedBlockUnion P owner j
    (∀ j,(filled j).Nonempty) ∧
    (∀ i j,i≠j → Disjoint (filled i) (filled j)) ∧
    Finset.univ.biUnion filled=(Finset.univ.biUnion root)∪P.biUnion id := by
  classical
  let filled := fun j => root j∪assignedBlockUnion P owner j
  have hsub (j : J) : assignedBlockUnion P owner j⊆P.biUnion id := by
    intro x hx
    obtain ⟨S,_,hx⟩ := (mem_assignedBlockUnion P owner j x).mp hx
    exact Finset.mem_biUnion.mpr ⟨S.val,S.property,hx⟩
  have ha : ∀ i j,i≠j → Disjoint (assignedBlockUnion P owner i) (assignedBlockUnion P owner j) := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨S,hS,hx⟩ := (mem_assignedBlockUnion P owner i x).mp hx
    obtain ⟨T,hT,hy⟩ := (mem_assignedBlockUnion P owner j x).mp hy
    by_cases hST : S.val=T.val
    · have he : S=T := Subtype.ext hST
      exact hij (hS.symm.trans (he ▸ hT))
    · exact Finset.disjoint_left.mp (hP S.val S.property T.val T.property hST) hx hy
  refine ⟨?_,?_,?_⟩
  · intro j
    exact (hne j).mono Finset.subset_union_left
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro x hx hy
    rcases Finset.mem_union.mp hx with hx | hx <;> rcases Finset.mem_union.mp hy with hy | hy
    · exact Finset.disjoint_left.mp (hroots i j hij) hx hy
    · exact Finset.disjoint_left.mp (hrootP i) hx (hsub j hy)
    · exact Finset.disjoint_left.mp (hrootP j) hy (hsub i hx)
    · exact Finset.disjoint_left.mp (ha i j hij) hx hy
  · ext x
    constructor
    · intro hx
      obtain ⟨j,_,hx⟩ := Finset.mem_biUnion.mp hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ j,hx⟩)
      · exact Finset.mem_union_right _ (hsub j hx)
    · intro hx
      rcases Finset.mem_union.mp hx with hx | hx
      · obtain ⟨j,_,hx⟩ := Finset.mem_biUnion.mp hx
        exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ j,Finset.mem_union_left _ hx⟩
      · obtain ⟨S,hS,hx⟩ := Finset.mem_biUnion.mp hx
        let t : {S // S∈P} := ⟨S,hS⟩
        exact Finset.mem_biUnion.mpr ⟨owner t,Finset.mem_univ _,Finset.mem_union_right _
          ((mem_assignedBlockUnion P owner (owner t) x).mpr ⟨t,rfl,hx⟩)⟩

end MinorFreeSpanners
