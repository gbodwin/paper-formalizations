import MinorFreeSpanners.ResidualOwnershipPartition

/-! Restrict actual boundary ownership to a chosen family of whole residual
components. The other components stay outside every expanded root carrier. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
namespace ResidualOwnership
variable {I : Type*} [Fintype I] {H : SimpleGraph I} {roots : Finset I}

noncomputable def chosenComponents (O : ResidualOwnership H roots)
    (F : Finset (H.induce ((Finset.univ\roots : Finset I):Set I)).ConnectedComponent)
    (r : {r // r∈roots}) := F.filter (fun t => O.owner t=r)

noncomputable def chosenAbsorbed (O : ResidualOwnership H roots)
    (F : Finset (H.induce ((Finset.univ\roots : Finset I):Set I)).ConnectedComponent)
    (r : {r // r∈roots}) :=
  (O.chosenComponents F r).biUnion (ResidualComponents.block H (Finset.univ\roots))

noncomputable def chosenFilled (O : ResidualOwnership H roots)
    (F : Finset (H.induce ((Finset.univ\roots : Finset I):Set I)).ConnectedComponent)
    (r : {r // r∈roots}) := insert r.val (O.chosenAbsorbed F r)

 theorem chosenAbsorbed_subset (O : ResidualOwnership H roots)
    (F : Finset (H.induce ((Finset.univ\roots : Finset I):Set I)).ConnectedComponent)
    (r : {r // r∈roots}) : O.chosenAbsorbed F r⊆O.absorbed r := by
  classical
  intro i hi
  obtain ⟨t,ht,hit⟩ := Finset.mem_biUnion.mp hi
  exact (O.mem_absorbed r i).mpr ⟨t,(Finset.mem_filter.mp ht).2,hit⟩

 theorem chosenFilled_subset (O : ResidualOwnership H roots)
    (F : Finset (H.induce ((Finset.univ\roots : Finset I):Set I)).ConnectedComponent)
    (r : {r // r∈roots}) : O.chosenFilled F r⊆O.filled r :=
  Finset.insert_subset_insert r.val (O.chosenAbsorbed_subset F r)

 theorem chosenFilled_disjoint (O : ResidualOwnership H roots)
    (F : Finset (H.induce ((Finset.univ\roots : Finset I):Set I)).ConnectedComponent)
    (r s : {r // r∈roots}) (hrs : r≠s) :
    Disjoint (O.chosenFilled F r) (O.chosenFilled F s) :=
  (O.filled_disjoint r s hrs).mono (O.chosenFilled_subset F r) (O.chosenFilled_subset F s)

 theorem chosenFilled_union (O : ResidualOwnership H roots)
    (F : Finset (H.induce ((Finset.univ\roots : Finset I):Set I)).ConnectedComponent) :
    (Finset.univ.biUnion (O.chosenFilled F))=
      roots∪F.biUnion (ResidualComponents.block H (Finset.univ\roots)) := by
  classical
  ext i
  constructor
  · intro hi
    obtain ⟨r,_,hr⟩ := Finset.mem_biUnion.mp hi
    rcases Finset.mem_insert.mp hr with he|he
    · exact Finset.mem_union_left _ (he ▸ r.property)
    · obtain ⟨t,ht,hit⟩ := Finset.mem_biUnion.mp he
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨t,(Finset.mem_filter.mp ht).1,hit⟩)
  · intro hi
    rcases Finset.mem_union.mp hi with hi|hi
    · exact Finset.mem_biUnion.mpr ⟨⟨i,hi⟩,mem_univ _,Finset.mem_insert_self _ _⟩
    · obtain ⟨t,ht,hit⟩ := Finset.mem_biUnion.mp hi
      exact Finset.mem_biUnion.mpr ⟨O.owner t,mem_univ _,Finset.mem_insert_of_mem
        (Finset.mem_biUnion.mpr ⟨t,Finset.mem_filter.mpr ⟨ht,rfl⟩,hit⟩)⟩

 theorem unchosen_block_disjoint (O : ResidualOwnership H roots)
    (F : Finset (H.induce ((Finset.univ\roots : Finset I):Set I)).ConnectedComponent)
    (t : (H.induce ((Finset.univ\roots : Finset I):Set I)).ConnectedComponent) (ht : t∉F)
    (r : {r // r∈roots}) :
    Disjoint (ResidualComponents.block H (Finset.univ\roots) t) (O.chosenFilled F r) := by
  classical
  apply Finset.disjoint_left.mpr
  intro i hi hj
  rcases Finset.mem_insert.mp hj with hj|hj
  · exact (Finset.mem_sdiff.mp (ResidualComponents.subset H _ t hi)).2 (hj ▸ r.property)
  · obtain ⟨q,hq,hiq⟩ := Finset.mem_biUnion.mp hj
    exact Finset.disjoint_left.mp (ResidualComponents.disjoint H _ t q
      (fun he => ht (he.symm ▸ (Finset.mem_filter.mp hq).1))) hi hiq

end ResidualOwnership
end MinorFreeSpanners
