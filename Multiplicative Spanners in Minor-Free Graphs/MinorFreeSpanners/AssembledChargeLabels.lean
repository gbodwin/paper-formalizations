import MinorFreeSpanners.AssembledLargeBlockCredit
import MinorFreeSpanners.OwnedBlockPartition

/-! The charged old labels are the actual donors, endpoint blocks, active
absorbed blocks and large leftovers from one common root-fiber construction. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable
namespace AssembledPathFamilies
variable {I V : Type*} [Fintype I] {B T G : SimpleGraph V} {w : Sym2 V → ℝ} {D₀ : ℝ}
variable {C : ClusterFamily (I:=I) B w D₀} {hB : B≤G} {hT : T≤G}
variable {H : SimpleGraph I} {hH : H≤C.graph T} {roots : Finset I}
variable (O : ResidualOwnership H roots)
variable {d credit : I → ℝ} {M L c b a : ℝ} {spare future : {r // r∈roots} → ℝ} {N : ℕ}
variable (Q : (r : {r // r∈roots}) → RootedPathAssemblyResult C hB hT H hH
    (Finset.univ\roots) r.val (O.components r) O.port d credit M L c b a (spare r) (future r) N)

noncomputable def rootCharge (active : Finset (Finset I))
    (owner : {S // S∈active} → {r // r∈roots}) (r : {r // r∈roots}) : Finset I := by
  classical
  exact (O.components r).biUnion (Q r).selected ∪ (O.components r).biUnion (Q r).ends ∪
    assignedBlockUnion active owner r

noncomputable def largeLeftovers : Finset (Finset I) := by
  classical
  exact (leftovers O Q).filter (fun S => N<S.card)

noncomputable def chargeLabels (active : Finset (Finset I))
    (owner : {S // S∈active} → {r // r∈roots}) : Finset I := by
  classical
  exact Finset.univ.biUnion (rootCharge O Q active owner) ∪ (largeLeftovers O Q).biUnion id

 theorem selected_subset_charge (active : Finset (Finset I))
    (owner : {S // S∈active} → {r // r∈roots}) (r : {r // r∈roots}) :
    (O.components r).biUnion (Q r).selected⊆chargeLabels O Q active owner := by
  classical
  intro i hi
  exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨r,Finset.mem_univ _,
    Finset.mem_union_left _ (Finset.mem_union_left _ hi)⟩)

 theorem active_subset_charge (active : Finset (Finset I))
    (owner : {S // S∈active} → {r // r∈roots}) :
    active.biUnion id⊆chargeLabels O Q active owner := by
  classical
  intro i hi
  obtain ⟨S,hS,hi⟩ := Finset.mem_biUnion.mp hi
  let t : {S // S∈active} := ⟨S,hS⟩
  exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨owner t,Finset.mem_univ _,
    Finset.mem_union_right _ ((mem_assignedBlockUnion active owner (owner t) i).mpr ⟨t,rfl,hi⟩)⟩)

 theorem allPaid_subset_charge (active : Finset (Finset I))
    (owner : {S // S∈active} → {r // r∈roots}) :
    allPaidLabels O Q⊆chargeLabels O Q active owner := by
  classical
  intro i hi
  obtain ⟨t,_,hi⟩ := Finset.mem_biUnion.mp hi
  let r := O.owner t
  have ht : t∈O.components r := by simp [ResidualOwnership.components,r]
  rcases Finset.mem_union.mp hi with hi | hi
  · rcases Finset.mem_union.mp hi with hi | hi
    · exact selected_subset_charge O Q active owner r (Finset.mem_biUnion.mpr ⟨t,ht,hi⟩)
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨r,Finset.mem_univ _,
        Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨t,ht,hi⟩))⟩)
  · obtain ⟨S,hS,hi⟩ := Finset.mem_biUnion.mp hi
    obtain ⟨hS,hlarge⟩ := Finset.mem_filter.mp hS
    by_cases hs : S∈(O.components r).image (Q r).selected
    · obtain ⟨u,hu,he⟩ := Finset.mem_image.mp hs
      exact selected_subset_charge O Q active owner r (Finset.mem_biUnion.mpr ⟨u,hu,he ▸ hi⟩)
    · have hleft : S∈leftovers O Q := Finset.mem_biUnion.mpr ⟨r,Finset.mem_univ _,
        Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨t,ht,hS⟩,hs⟩⟩
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨S,Finset.mem_filter.mpr ⟨hleft,hlarge⟩,hi⟩)

 theorem charge_subset_residual (active : Finset (Finset I)) (hactive : active⊆leftovers O Q)
    (owner : {S // S∈active} → {r // r∈roots}) :
    chargeLabels O Q active owner⊆Finset.univ\roots := by
  classical
  intro i hi
  rcases Finset.mem_union.mp hi with hi | hi
  · obtain ⟨r,_,hi⟩ := Finset.mem_biUnion.mp hi
    rcases Finset.mem_union.mp hi with hi | hi
    · rcases Finset.mem_union.mp hi with hi | hi
      · obtain ⟨t,ht,hi⟩ := Finset.mem_biUnion.mp hi
        apply ResidualComponents.subset H (Finset.univ\roots) t
        rw [←((Q r).partition t ht).cover]
        exact Finset.mem_biUnion.mpr ⟨(Q r).selected t,((Q r).partition t ht).member,hi⟩
      · obtain ⟨t,ht,hi⟩ := Finset.mem_biUnion.mp hi
        obtain ⟨x,y,p,_,_,he⟩ := ((Q r).partition t ht).actual_ends
        rw [he] at hi
        obtain ⟨S,hS,hi⟩ := Finset.mem_biUnion.mp hi
        apply ResidualComponents.subset H (Finset.univ\roots) t
        rw [←((Q r).partition t ht).cover]
        exact Finset.mem_biUnion.mpr ⟨S,(Finset.mem_filter.mp hS).1,hi⟩
    · obtain ⟨S,_,hi⟩ := (mem_assignedBlockUnion active owner r i).mp hi
      exact leftover_subset O Q (hactive S.property) hi
  · obtain ⟨S,hS,hi⟩ := Finset.mem_biUnion.mp hi
    exact leftover_subset O Q (Finset.mem_filter.mp hS).1 hi

end AssembledPathFamilies
end MinorFreeSpanners
