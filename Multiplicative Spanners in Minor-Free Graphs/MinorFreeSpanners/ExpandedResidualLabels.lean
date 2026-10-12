import MinorFreeSpanners.ExpandedRootOriginalGroups
import MinorFreeSpanners.SelectedResidualDegree
import MinorFreeSpanners.SelectedLabelPartition

/-! An original label left outside every expanded root is exactly an old
mixed residual singleton left outside the absorbed components. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

attribute [-instance] instDecidableEqSum in
 theorem residual_mem_originalMixedLabels {I : Type*}
    (P : Finset (Finset I)) (S : Finset (SelectedResidualIndex P))
    (i : {i // i∉P.biUnion id}) :
    i.val∈originalMixedLabels P S ↔ Sum.inr i∈S := by
  classical
  constructor
  · intro hi
    obtain ⟨j,hj,hij⟩ := Finset.mem_biUnion.mp hi
    cases j with
    | inl U => exact (i.property (Finset.mem_biUnion.mpr ⟨U.val,U.property,hij⟩)).elim
    | inr j =>
      have he : i.val=j.val := Finset.mem_singleton.mp hij
      exact (congrArg Sum.inr (Subtype.ext he)).symm ▸ hj
  · intro hi
    exact Finset.mem_biUnion.mpr ⟨Sum.inr i,hi,Finset.mem_singleton_self _⟩

attribute [-instance] instDecidableEqSum in
 theorem old_selected_subset_expanded {I : Type*} [Fintype I]
    (P : Finset (Finset I)) (S : Finset (SelectedResidualIndex P))
    (hroot : selectedRoots P⊆S) : P.biUnion id⊆originalMixedLabels P S := by
  classical
  intro i hi
  obtain ⟨U,hU,hi⟩ := Finset.mem_biUnion.mp hi
  exact Finset.mem_biUnion.mpr ⟨Sum.inl ⟨U,hU⟩,hroot (by simp [selectedRoots]),hi⟩

attribute [-instance] instDecidableEqSum in
noncomputable def expandedOldResidual {I : Type*} [Fintype I]
    (P : Finset (Finset I)) (S : Finset (SelectedResidualIndex P))
    (hroot : selectedRoots P⊆S) (i : {i // i∉originalMixedLabels P S}) :
    {i // i∉P.biUnion id} :=
  ⟨i.val,fun hi => i.property (old_selected_subset_expanded P S hroot hi)⟩

attribute [-instance] instDecidableEqSum in
 theorem expandedOldResidual_outside {I : Type*} [Fintype I]
    (P : Finset (Finset I)) (S : Finset (SelectedResidualIndex P))
    (hroot : selectedRoots P⊆S) (i : {i // i∉originalMixedLabels P S}) :
    Sum.inr (expandedOldResidual P S hroot i)∉S := by
  intro hi
  exact i.property ((residual_mem_originalMixedLabels P S _).mpr hi)

attribute [-instance] instDecidableEqSum in
 theorem chosenFilled_contains_roots {I : Type*} [Fintype I]
    {H : SimpleGraph I} {roots : Finset I} (O : ResidualOwnership H roots)
    (Q : Finset (H.induce ((Finset.univ\roots : Finset I):Set I)).ConnectedComponent) :
    roots⊆Finset.univ.biUnion (O.chosenFilled Q) := by
  classical
  intro i hi
  exact Finset.mem_biUnion.mpr ⟨⟨i,hi⟩,Finset.mem_univ _,Finset.mem_insert_self _ _⟩

end MinorFreeSpanners
