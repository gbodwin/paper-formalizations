import MinorFreeSpanners.SelectedClassReserve

/-! Convert scalar high/weak allocations to the exact selected-root budget
functions. The baseline is derived from a proved radius floor, while high roots
retain the additional allowance for heavy attachments. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

attribute [-instance] instDecidableEqSum in
 theorem selected_class_heavy_inputs {I : Type*} (P : Finset (Finset I))
    (high : Finset {S // S∈P}) (d : I → ℝ) (radius : {S // S∈P} → ℝ)
    (baseline c edgeMax a : ℝ) (N : ℕ)
    (highSpare weakSpare highReserve weakReserve highFuture weakFuture : ℝ)
    (hc : 0≤c) (hfloor : ∀ S,baseline≤radius S)
    (hsH : 0≤highSpare) (hsW : 0≤weakSpare)
    (hfH : 0≤highFuture) (hfW : 0≤weakFuture)
    (hrH : highFuture≤highReserve) (hrW : weakFuture≤weakReserve)
    (hattach : 2*c*edgeMax+2*(N:ℝ)*a+highFuture≤highReserve)
    (hbudgetH : 5*(N:ℝ)*a+highReserve≤highSpare)
    (hbudgetW : 5*(N:ℝ)*a+weakReserve≤weakSpare) :
    let spare := selectedClassValue P high highSpare weakSpare
    let reserve := selectedClassValue P high highReserve weakReserve
    let future := selectedClassValue P high highFuture weakFuture
    (∀ r,0≤spare r) ∧ (∀ r,0≤future r) ∧
    (∀ r,c*baseline≤c*(mixedEffectiveDiameter d radius r.val-1)+future r) ∧
    (∀ r,future r≤reserve r) ∧
    (∀ r,r∈selectedRootHigh P high → 2*c*edgeMax+2*(N:ℝ)*a+future r≤reserve r) ∧
    (∀ r,5*(N:ℝ)*a+reserve r≤spare r) := by
  intro spare reserve future
  have hs (r) : 0≤spare r := by
    dsimp [spare,selectedClassValue]
    split <;> assumption
  have hf (r) : 0≤future r := by
    dsimp [future,selectedClassValue]
    split <;> assumption
  refine ⟨hs,hf,?_,?_,?_,?_⟩
  · rintro ⟨r,hr⟩
    cases r with
    | inl S =>
      have hm := mul_le_mul_of_nonneg_left (hfloor S) hc
      have hh := hf ⟨Sum.inl S,hr⟩
      simp only [mixedEffectiveDiameter,Sum.elim_inl,add_sub_cancel_right]
      linarith
    | inr i => simp [selectedRoots] at hr
  · intro r
    dsimp [future,reserve,selectedClassValue]
    split <;> assumption
  · intro r hr
    simpa only [future,reserve,selectedClassValue,ite_eq_left hr] using hattach
  · intro r
    dsimp [spare,reserve,selectedClassValue]
    split <;> assumption

end MinorFreeSpanners
