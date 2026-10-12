import MinorFreeSpanners.SelectedRootSubtype
import MinorFreeSpanners.ActualGroupReindex
import MinorFreeSpanners.SelectedRootCreditTransfer

/-! The prior actual high/weak bill and the retained root credit keep their
meaning when indexed by mixed root vertices. No root is assigned fresh credit. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

attribute [-instance] instDecidableEqSum in
 theorem original_highRootEligible {I : Type*} (P : Finset (Finset I))
    (high : Finset {S // S∈P}) :
    originalMixedLabels P (highRootEligible P high)=high.biUnion Subtype.val := by
  classical
  ext i
  simp only [originalMixedLabels,highRootEligible,Finset.mem_biUnion,Finset.mem_image]
  constructor
  · rintro ⟨_,⟨S,hS,rfl⟩,hi⟩
    exact ⟨S,hS,hi⟩
  · rintro ⟨S,hS,hi⟩
    exact ⟨Sum.inl S,⟨S,hS,rfl⟩,hi⟩

attribute [-instance] instDecidableEqSum in
 theorem selected_prior_bill_reindex {I V : Type*} [Fintype I] [Fintype V]
    {A B G : SimpleGraph V} {w : Sym2 V → ℝ} {D E : ℝ}
    (C : ClusterFamily (I:=I) A w D) (P : Finset (Finset I))
    (F : ClusterFamily (I:={S // S∈P}) G w E)
    (hbranch : ∀ S,F.branch S={x | ∃ i∈S.val,x∈C.branch i})
    (high : Finset {S // S∈P}) (credit : SelectedResidualIndex P → ℝ) (resource : ℝ)
    (hprior : (∑ e∈C.touchingEdges B (originalMixedLabels P (weakRootPrior P high)),w e)+
      (∑ e∈C.markedEdges B (P.biUnion id\originalMixedLabels P (weakRootPrior P high)),w e)+
      (∑ i,credit i)≤resource) :
    (∑ e∈C.touchingEdges B (originalMixedLabels P ((Finset.univ\selectedRootHigh P high).image Subtype.val)),w e)+
      (∑ e∈C.markedEdges B (originalMixedLabels P ((selectedRootHigh P high).image Subtype.val)),w e)+
      (∑ i,credit i)≤resource := by
  classical
  have hdis : ∀ S U,S∈P → U∈P → S≠U → Disjoint S U := by
    intro S U hS hU hne
    exact C.original_groups_disjoint F Subtype.val hbranch ⟨S,hS⟩ ⟨U,hU⟩
      (fun he => hne (congrArg Subtype.val he))
  rw [selectedRootWeak_image,selectedRootHigh_image,original_highRootEligible,
    ←selected_high_labels P hdis high]
  exact hprior

attribute [-instance] instDecidableEqSum in
 theorem selected_root_spare_budget {I : Type*} (P : Finset (Finset I))
    (high : Finset {S // S∈P}) (d : I → ℝ) (keep radius : {S // S∈P} → ℝ)
    (old : I → ℝ) (c weakReserve R rootBound bill future : ℝ)
    (hweak : ∀ S,S∉high → keep S=c*radius S+weakReserve)
    (hhigh : ∀ S,S∈high → R≤keep S ∧ radius S=rootBound)
    (hweakBudget : bill+future≤weakReserve) (hhighBudget : c*rootBound+bill+future≤R) :
    ∀ r : {r // r∈selectedRoots P},bill+future≤
      selectedResidualCredit P keep old r.val-c*(mixedEffectiveDiameter d radius r.val-1) := by
  classical
  rintro ⟨j,hj⟩
  cases j with
  | inl S =>
    change bill+future≤keep S-c*((radius S+1)-1)
    by_cases hS : S∈high
    · have hh := hhigh S hS
      rw [hh.2]
      linarith
    · rw [hweak S hS]
      linarith
  | inr i => simp [selectedRoots] at hj

end MinorFreeSpanners
