import MinorFreeSpanners.PartialResidualOwnership
import MinorFreeSpanners.ConnectedComponentSlice

/-! Removing exactly the chosen whole residual components leaves exactly the
unchosen whole components. Their actual old spanning paths are retained. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
namespace ResidualOwnership
variable {I : Type*} [Fintype I] {H : SimpleGraph I} {roots : Finset I}

 theorem unchosen_union (O : ResidualOwnership H roots)
    (Q : Finset (H.induce ((Finset.univ\roots : Finset I):Set I)).ConnectedComponent) :
    Finset.univ\Finset.univ.biUnion (O.chosenFilled Q)=
      (Finset.univ\Q).biUnion (ResidualComponents.block H (Finset.univ\roots)) := by
  classical
  rw [O.chosenFilled_union Q]
  apply Finset.Subset.antisymm
  · intro i hi
    have hn := (Finset.mem_sdiff.mp hi).2
    have hir : i∈Finset.univ\roots := Finset.mem_sdiff.mpr ⟨mem_univ _,
      fun hh => hn (Finset.mem_union_left _ hh)⟩
    obtain ⟨t,hit⟩ := ResidualComponents.covers H _ hir
    refine Finset.mem_biUnion.mpr ⟨t,Finset.mem_sdiff.mpr ⟨mem_univ _,?_⟩,hit⟩
    intro ht
    exact hn (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨t,ht,hit⟩))
  · intro i hi
    obtain ⟨t,ht,hit⟩ := Finset.mem_biUnion.mp hi
    refine Finset.mem_sdiff.mpr ⟨mem_univ _,?_⟩
    intro hi
    rcases Finset.mem_union.mp hi with hi|hi
    · exact (Finset.mem_sdiff.mp (ResidualComponents.subset H _ t hit)).2 hi
    · obtain ⟨q,hq,hiq⟩ := Finset.mem_biUnion.mp hi
      exact Finset.disjoint_left.mp (ResidualComponents.disjoint H _ t q
        (fun he => (Finset.mem_sdiff.mp ht).2 (he.symm ▸ hq))) hit hiq

 theorem unchosen_components (O : ResidualOwnership H roots)
    (Q : Finset (H.induce ((Finset.univ\roots : Finset I):Set I)).ConnectedComponent) :
    ∀ q : (H.induce ((Finset.univ\Finset.univ.biUnion (O.chosenFilled Q) : Finset I):Set I)).ConnectedComponent,
      ∃ t,t∉Q ∧
        ResidualComponents.block H (Finset.univ\Finset.univ.biUnion (O.chosenFilled Q)) q=
          ResidualComponents.block H (Finset.univ\roots) t := by
  classical
  rw [O.unchosen_union Q]
  intro q
  obtain ⟨t,ht,he⟩ := (chosen_slices_are_components H (Finset.univ\roots)
    (Finset.univ\Q) (ResidualComponents.block H (Finset.univ\roots))
    (by intros;exact Finset.Subset.refl _)
    (fun t _ => ResidualComponents.nonempty H _ t)
    (fun t _ => ResidualComponents.connected H _ t)).2 q
  exact ⟨t,(Finset.mem_sdiff.mp ht).2,he⟩

end ResidualOwnership
end MinorFreeSpanners
