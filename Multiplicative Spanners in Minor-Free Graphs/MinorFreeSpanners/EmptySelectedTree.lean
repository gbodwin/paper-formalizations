import MinorFreeSpanners.SelectedResidualClusters
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! If the actual selected-root family is empty, the retained common tree
still supplies a genuine tree on all original labels. No root nonemptiness is
inferred from a size, diameter, or weighted-girth premise. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

 theorem original_tree_of_empty_selected {I : Type*} (P : Finset (Finset I))
    (H : SimpleGraph I) (K : SimpleGraph (SelectedResidualIndex P))
    (hempty : P=∅) (hK : K.IsTree) (hforest : H.IsAcyclic)
    (hres : ∀ i j : {i // i∉P.biUnion id},K.Adj (Sum.inr i) (Sum.inr j) ↔ H.Adj i.val j.val) :
    H.IsTree := by
  subst P
  let f : SelectedResidualIndex (∅ : Finset (Finset I)) → I :=
    Sum.elim (fun S : {S : Finset I // S∈(∅ : Finset (Finset I))} =>
      False.elim (Finset.notMem_empty S.val S.property)) Subtype.val
  let hom : K →g H := {
    toFun := f
    map_rel' := by
      intro a b hab
      cases a with
      | inl S => exact False.elim (Finset.notMem_empty S.val S.property)
      | inr i =>
        cases b with
        | inl S => exact False.elim (Finset.notMem_empty S.val S.property)
        | inr j => exact (hres i j).mp hab }
  have hsurj : Function.Surjective hom := by
    intro i
    exact ⟨Sum.inr ⟨i,by simp⟩,rfl⟩
  exact ⟨hK.connected.map hom hsurj,hforest⟩

end MinorFreeSpanners
