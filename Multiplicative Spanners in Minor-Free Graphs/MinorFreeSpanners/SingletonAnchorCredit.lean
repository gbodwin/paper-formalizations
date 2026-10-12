import MinorFreeSpanners.SelectedRootCreditTransfer

/-! The extra credit of an artificial singleton high root is charged exactly
once. No existing residual credit is removed, and no injected credit is claimed
to have come from an edge or from a previous retained reserve. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

noncomputable def anchorInjectedCredit {I : Type*} (credit : I → ℝ) (anchor : I)
    (injection : ℝ) : I → ℝ := by
  classical
  exact fun i => credit i + if i=anchor then injection else 0

 theorem anchorInjectedCredit_sum {I : Type*} [Fintype I] (credit : I → ℝ)
    (anchor : I) (injection : ℝ) :
    (∑ i,anchorInjectedCredit credit anchor injection i)=(∑ i,credit i)+injection := by
  classical
  simp [anchorInjectedCredit,Finset.sum_add_distrib]

 theorem singleton_anchor_mixed_credit_sum {I : Type*} [Fintype I]
    (credit : I → ℝ) (anchor : I) (injection : ℝ) :
    (∑ i,selectedResidualCredit {{anchor}} (fun _ => credit anchor+injection) credit i)=
      (∑ i,credit i)+injection := by
  classical
  rw [selectedResidualCredit_sum]
  have hroot : (∑ S : {S : Finset I // S∈({{anchor}} : Finset (Finset I))},
      (credit anchor+injection))=credit anchor+injection := by
    rw [←Finset.sum_subtype ({{anchor}} : Finset (Finset I)) (by simp)
      (fun _ => credit anchor+injection)]
    simp
  rw [hroot]
  have hsplit := Finset.sum_sdiff (f:=credit) (Finset.subset_univ ({anchor} : Finset I))
  have hu : ({{anchor}} : Finset (Finset I)).biUnion id={anchor} := by
    ext i
    simp
  rw [hu]
  simp only [Finset.sum_singleton] at hsplit
  linarith

 theorem singleton_anchor_credit_budget {I : Type*} [Fintype I]
    (credit : I → ℝ) (anchor : I) (injection : ℝ) :
    (∑ i,selectedResidualCredit {{anchor}} (fun _ => credit anchor+injection) credit i)=
      ∑ i,anchorInjectedCredit credit anchor injection i := by
  rw [singleton_anchor_mixed_credit_sum,anchorInjectedCredit_sum]

end MinorFreeSpanners
