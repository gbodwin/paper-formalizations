import MinorFreeSpanners.SingletonAnchorEdges
import MinorFreeSpanners.SingletonAnchorCredit
import MinorFreeSpanners.SelectedRootBudget

/-! The artificial singleton root's exact original bill is paid by the
explicit injection. It has no weak-root touching bill or internal heavy edge;
edges from the anchor to residual labels are reserved for later absorption. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

attribute [-instance] instDecidableEqSum in
 theorem singleton_anchor_prior_ledger {I V : Type*} [Fintype I] [Fintype V]
    {A B G : SimpleGraph V} {w : Sym2 V → ℝ} {D E : ℝ}
    (C : ClusterFamily (I:=I) A w D) (anchor : I)
    (F : ClusterFamily (I:={S : Finset I // S∈({{anchor}} : Finset (Finset I))}) G w E)
    (hbranch : ∀ S,F.branch S={x | ∃ i∈S.val,x∈C.branch i})
    (credit : I → ℝ) (injection : ℝ)
    (hloop : ∀ i x,x∈C.branch i → ∀ y,y∈C.branch i → ¬B.Adj x y) :
    let P : Finset (Finset I) := {{anchor}}
    let high := selectedRootHigh P (Finset.univ : Finset {S // S∈P})
    (∑ e∈C.touchingEdges B (originalMixedLabels P ((Finset.univ\high).image Subtype.val)),w e)+
      (∑ e∈C.markedEdges B (originalMixedLabels P (high.image Subtype.val)),w e)+
      (∑ i,selectedResidualCredit P (fun _ => credit anchor+injection) credit i)≤
        ∑ i,anchorInjectedCredit credit anchor injection i := by
  classical
  dsimp only
  apply selected_prior_bill_reindex C {{anchor}} F hbranch Finset.univ
  have hu : ({{anchor}} : Finset (Finset I)).biUnion id={anchor} := by
    ext i
    simp
  simp only [weakRootPrior,Finset.sdiff_self,Finset.image_empty,originalMixedLabels,
    Finset.biUnion_empty,Finset.sdiff_empty]
  have hm : C.markedEdges B (({{anchor}} : Finset (Finset I)).biUnion id)=∅ := by
    rw [hu]
    exact C.markedEdges_singleton_empty hloop anchor
  rw [hm]
  have he : C.touchingEdges B ∅=∅ := by
    ext e
    simp [ClusterFamily.touchingEdges]
  simp only [he,Finset.sum_empty,zero_add,singleton_anchor_credit_budget,le_refl]

end MinorFreeSpanners
