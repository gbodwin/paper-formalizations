import MinorFreeSpanners.OwnedBlockPartition

/-! Blocks with no unpaid heavy edge are retained as their own output carriers.
Together with the simultaneously enlarged roots, they still partition every
original root and path-block label, with no deleted small or isolated block. -/
namespace MinorFreeSpanners
open Finset
attribute [local instance] Classical.propDecidable

 theorem retained_inactive_partition {I J : Type*} [Fintype J]
    (P active : Finset (Finset I)) (hactive : active⊆P)
    (root : J → Finset I) (owner : {S // S∈active} → J)
    (hne : ∀ j,(root j).Nonempty) (hPne : ∀ S∈P,S.Nonempty)
    (hroots : ∀ i j,i≠j → Disjoint (root i) (root j))
    (hrootP : ∀ j,Disjoint (root j) (P.biUnion id))
    (hP : ∀ S∈P,∀ T∈P,S≠T → Disjoint S T) :
    let carrier : J⊕{S // S∈P\active} → Finset I :=
      Sum.elim (fun j => root j∪assignedBlockUnion active owner j) Subtype.val
    (∀ j,(carrier j).Nonempty) ∧
    (∀ i j,i≠j → Disjoint (carrier i) (carrier j)) ∧
    Finset.univ.biUnion carrier=(Finset.univ.biUnion root)∪P.biUnion id := by
  classical
  let filled := fun j => root j∪assignedBlockUnion active owner j
  have hAP : active.biUnion id⊆P.biUnion id := by
    intro i hi
    obtain ⟨S,hS,hi⟩ := Finset.mem_biUnion.mp hi
    exact Finset.mem_biUnion.mpr ⟨S,hactive hS,hi⟩
  have hp := owned_block_partition active root owner hne hroots
    (fun j => (hrootP j).mono_right hAP)
    (fun S hS T hT => hP S (hactive hS) T (hactive hT))
  have hcross (j : J) (S : {S // S∈P\active}) : Disjoint (filled j) S.val := by
    apply Finset.disjoint_left.mpr
    intro i hi hS
    obtain ⟨hSP,hSa⟩ := Finset.mem_sdiff.mp S.property
    rcases Finset.mem_union.mp hi with hi | hi
    · exact Finset.disjoint_left.mp (hrootP j) hi (Finset.mem_biUnion.mpr ⟨S.val,hSP,hS⟩)
    · obtain ⟨U,_,hi⟩ := (mem_assignedBlockUnion active owner j i).mp hi
      have hUS : U.val≠S.val := fun he => hSa (he ▸ U.property)
      exact Finset.disjoint_left.mp (hP U.val (hactive U.property) S.val hSP hUS) hi hS
  refine ⟨?_,?_,?_⟩
  · intro j
    cases j with
    | inl j => exact hp.1 j
    | inr S => exact hPne S.val (Finset.mem_sdiff.mp S.property).1
  · intro i j hij
    cases i with
    | inl i =>
      cases j with
      | inl j => exact hp.2.1 i j (fun he => hij (he ▸ rfl))
      | inr S => exact hcross i S
    | inr S =>
      cases j with
      | inl j => exact (hcross j S).symm
      | inr U =>
        exact hP S.val (Finset.mem_sdiff.mp S.property).1 U.val
          (Finset.mem_sdiff.mp U.property).1 (fun he => hij (congrArg Sum.inr (Subtype.ext he)))
  · ext i
    constructor
    · intro hi
      obtain ⟨j,_,hi⟩ := Finset.mem_biUnion.mp hi
      cases j with
      | inl j =>
        have hh : i∈Finset.univ.biUnion filled := Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,hi⟩
        rw [hp.2.2] at hh
        exact (Finset.union_subset_union subset_rfl hAP) hh
      | inr S =>
        exact Finset.mem_union_right _
          (Finset.mem_biUnion.mpr ⟨S.val,(Finset.mem_sdiff.mp S.property).1,hi⟩)
    · intro hi
      rcases Finset.mem_union.mp hi with hi | hi
      · obtain ⟨j,_,hi⟩ := Finset.mem_biUnion.mp hi
        exact Finset.mem_biUnion.mpr ⟨Sum.inl j,Finset.mem_univ _,Finset.mem_union_left _ hi⟩
      · obtain ⟨S,hS,hi⟩ := Finset.mem_biUnion.mp hi
        by_cases ha : S∈active
        · let s : {S // S∈active} := ⟨S,ha⟩
          exact Finset.mem_biUnion.mpr ⟨Sum.inl (owner s),Finset.mem_univ _,
            Finset.mem_union_right _ ((mem_assignedBlockUnion active owner (owner s) i).mpr ⟨s,rfl,hi⟩)⟩
        · exact Finset.mem_biUnion.mpr ⟨Sum.inr ⟨S,Finset.mem_sdiff.mpr ⟨hS,ha⟩⟩,
            Finset.mem_univ _,hi⟩

end MinorFreeSpanners
