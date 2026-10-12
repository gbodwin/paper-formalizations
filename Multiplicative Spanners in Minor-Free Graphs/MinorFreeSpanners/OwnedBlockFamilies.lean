import MinorFreeSpanners.OwnedBlockPartition

/-! The actual owner map determines finite block families. Their unions are
exactly the old-label carriers used by the simultaneous partition theorem. -/
namespace MinorFreeSpanners
open Finset
attribute [local instance] Classical.propDecidable

noncomputable def ownedBlocks {I J : Type*} (P : Finset (Finset I))
    (owner : {S // S∈P} → J) (j : J) : Finset (Finset I) := by
  classical
  exact (Finset.univ.filter (fun S : {S // S∈P} => owner S=j)).image Subtype.val

 theorem mem_ownedBlocks {I J : Type*} (P : Finset (Finset I))
    (owner : {S // S∈P} → J) (j : J) (S : Finset I) :
    S∈ownedBlocks P owner j ↔ ∃ hS : S∈P,owner ⟨S,hS⟩=j := by
  classical
  simp only [ownedBlocks,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨⟨U,hU⟩,ho,he⟩
    cases he
    exact ⟨hU,ho⟩
  · rintro ⟨hS,ho⟩
    exact ⟨⟨S,hS⟩,ho,rfl⟩

 theorem ownedBlocks_subset {I J : Type*} (P : Finset (Finset I))
    (owner : {S // S∈P} → J) (j : J) : ownedBlocks P owner j⊆P := by
  intro S hS
  exact ((mem_ownedBlocks P owner j S).mp hS).choose

 theorem ownedBlocks_union {I J : Type*} (P : Finset (Finset I))
    (owner : {S // S∈P} → J) (j : J) :
    (ownedBlocks P owner j).biUnion id=assignedBlockUnion P owner j := by
  classical
  ext x
  simp only [Finset.mem_biUnion,mem_ownedBlocks,mem_assignedBlockUnion]
  constructor
  · rintro ⟨S,⟨hS,ho⟩,hx⟩
    exact ⟨⟨S,hS⟩,ho,hx⟩
  · rintro ⟨⟨S,hS⟩,ho,hx⟩
    exact ⟨S,⟨hS,ho⟩,hx⟩

 theorem ownedBlocks_union_subset {I J : Type*} (P : Finset (Finset I))
    (owner : {S // S∈P} → J) (j : J) :
    (ownedBlocks P owner j).biUnion id⊆P.biUnion id := by
  classical
  intro i hi
  obtain ⟨S,hS,hi⟩ := Finset.mem_biUnion.mp hi
  exact Finset.mem_biUnion.mpr ⟨S,ownedBlocks_subset P owner j hS,hi⟩

end MinorFreeSpanners
