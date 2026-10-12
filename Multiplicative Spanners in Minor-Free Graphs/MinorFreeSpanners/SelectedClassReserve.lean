import MinorFreeSpanners.SelectedRootBudget

/-! Preserve separate high-root and weak-root credit after short absorption.
The choice is made by the actual selected-root flag, not by a new classification
or a uniform reserve that could discard the high-root surplus. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

attribute [-instance] instDecidableEqSum in
noncomputable def selectedClassValue {I : Type*} (P : Finset (Finset I))
    (high : Finset {S // S∈P}) (highValue weakValue : ℝ)
    (r : {r // r∈selectedRoots P}) : ℝ :=
  if r∈selectedRootHigh P high then highValue else weakValue

attribute [-instance] instDecidableEqSum in
 theorem selected_root_class_spare {I : Type*} (P : Finset (Finset I))
    (high : Finset {S // S∈P}) (d : I → ℝ) (keep radius : {S // S∈P} → ℝ)
    (old : I → ℝ) (c weakReserve R rootBound bill highFuture weakFuture : ℝ)
    (hweak : ∀ S,S∉high → keep S=c*radius S+weakReserve)
    (hhigh : ∀ S,S∈high → R≤keep S ∧ radius S=rootBound)
    (hweakBudget : bill+weakFuture≤weakReserve)
    (hhighBudget : c*rootBound+bill+highFuture≤R) :
    ∀ r : {r // r∈selectedRoots P},bill+selectedClassValue P high highFuture weakFuture r≤
      selectedResidualCredit P keep old r.val-c*(mixedEffectiveDiameter d radius r.val-1) := by
  classical
  rintro ⟨j,hj⟩
  cases j with
  | inl S =>
    have hclass : (⟨Sum.inl S,hj⟩ : {r // r∈selectedRoots P})∈selectedRootHigh P high ↔ S∈high := by
      constructor
      · intro h
        obtain ⟨Z,hZ,he⟩ := Finset.mem_image.mp h
        have hz : Z=S := Sum.inl.inj (congrArg Subtype.val he)
        exact hz ▸ hZ
      · intro h
        exact Finset.mem_image.mpr ⟨S,h,Subtype.ext rfl⟩
    change bill+(if _ then highFuture else weakFuture)≤keep S-c*((radius S+1)-1)
    by_cases hS : S∈high
    · rw [ite_eq_left (hclass.mpr hS)]
      have hh := hhigh S hS
      rw [hh.2]
      linarith
    · rw [ite_eq_right (fun h => hS (hclass.mp h)),hweak S hS]
      linarith
  | inr i => simp [selectedRoots] at hj

end MinorFreeSpanners
