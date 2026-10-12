import MinorFreeSpanners.SelectedResidualClusters
import MinorFreeSpanners.ExactConnectorPooling

/-! The retained mixed credit is the actual root credit together with every
unchanged residual old credit. A proved selected-root payment certificate then
extends to the whole old credit ledger without discarding or duplicating credit. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I]

noncomputable def selectedResidualCredit (P : Finset (Finset I))
    (root : {S // S∈P} → ℝ) (old : I → ℝ) : SelectedResidualIndex P → ℝ :=
  Sum.elim root (fun i => old i.val)

 theorem selectedResidualCredit_sum (P : Finset (Finset I))
    (root : {S // S∈P} → ℝ) (old : I → ℝ) :
    (∑ i,selectedResidualCredit P root old i)=
      (∑ S,root S)+(∑ i∈Finset.univ\P.biUnion id,old i) := by
  classical
  rw [Fintype.sum_sum_type]
  simp only [selectedResidualCredit,Sum.elim_inl,Sum.elim_inr]
  congr 1
  exact (Finset.sum_subtype (Finset.univ\P.biUnion id) (by simp) old).symm

 theorem selected_root_credit_transfer (P : Finset (Finset I))
    (root : {S // S∈P} → ℝ) (old : I → ℝ) (bill resource : ℝ)
    (hpaid : bill+(∑ S,root S)≤(∑ i∈P.biUnion id,old i)+resource) :
    bill+(∑ i,selectedResidualCredit P root old i)≤(∑ i,old i)+resource := by
  classical
  rw [selectedResidualCredit_sum]
  have he := Finset.sum_sdiff (f:=old) (Finset.subset_univ (P.biUnion id))
  linarith

end MinorFreeSpanners
