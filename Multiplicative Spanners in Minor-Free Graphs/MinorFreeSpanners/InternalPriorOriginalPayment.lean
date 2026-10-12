import MinorFreeSpanners.RetainedConnectorInternality
import MinorFreeSpanners.PriorPhaseOriginalPartition

/-! An arbitrary literal prior connector bag internal to the current roots
is disjoint from every later connector. This admits the actual retained union
from short absorption, without changing any earlier edge representative. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable
namespace ClusterFamily
variable {I V J : Type*} [Fintype I] [Fintype V] [Fintype J]
variable {A T E G : SimpleGraph V} {w : Sym2 V → ℝ} {D D₁ : ℝ}

attribute [-instance] instDecidableEqSum in
 theorem internal_prior_original_payment (C : ClusterFamily (I:=I) A w D)
    (hA : A≤G) (hT : T≤G) (P : Finset (Finset I))
    (F : ClusterFamily (I:={S // S∈P}) G w D₁)
    (hbranch : ∀ S,F.branch S={x | ∃ i∈S.val,x∈C.branch i})
    (hcover : ∀ x,∃ i,x∈C.branch i)
    (priorEdges : Finset (Sym2 V))
    (hinternal : ∀ e∈priorEdges,∃ g x y,x∈F.branch g ∧ y∈F.branch g ∧ e=s(x,y))
    (newH : J → SimpleGraph (SelectedResidualIndex P))
    (hnewH : ∀ j,newH j≤(C.selectedResidual hA P F hbranch).graph T)
    (carrier : J → Finset (SelectedResidualIndex P))
    (prior : Finset (SelectedResidualIndex P)) (credit : SelectedResidualIndex P → ℝ)
    (initial future c : ℝ)
    (hprior : (∑ e∈C.touchingEdges E (originalMixedLabels P prior),w e)+
      (∑ e∈C.markedEdges E (P.biUnion id\originalMixedLabels P prior),w e)+
      (∑ i,credit i)≤ initial+c*(∑ e∈priorEdges,w e))
    (hresidual : (∑ e∈(C.selectedResidual hA P F hbranch).unpaidTouchingEdges E
      (Finset.univ\selectedRoots P) prior,w e)+future≤(∑ i,credit i)+
      c*(∑ e∈(C.selectedResidual hA P F hbranch).connectorPool le_rfl hT newH hnewH carrier,w e)) :
    Disjoint priorEdges ((C.selectedResidual hA P F hbranch).connectorPool le_rfl hT newH hnewH carrier) ∧
    (∑ e∈E.edgeFinset,w e)+future≤ initial+
      c*(∑ e∈priorEdges∪(C.selectedResidual hA P F hbranch).connectorPool le_rfl hT newH hnewH carrier,w e) := by
  classical
  have hd := (C.selectedResidual hA P F hbranch).connectorPool_disjoint_internal le_rfl hT
    newH hnewH carrier priorEdges (by
      intro e he
      obtain ⟨g,x,y,hx,hy,heq⟩ := hinternal e he
      exact ⟨Sum.inl g,x,y,hx,hy,heq⟩)
  refine ⟨hd,?_⟩
  rw [Finset.sum_union hd]
  have he : (∑ e∈E.edgeFinset,w e)=(∑ e∈C.touchingEdges E (originalMixedLabels P prior),w e)+
      (∑ e∈C.markedEdges E (P.biUnion id\originalMixedLabels P prior),w e)+
      ∑ e∈(C.selectedResidual hA P F hbranch).unpaidTouchingEdges E
        (Finset.univ\selectedRoots P) prior,w e := by
    convert C.mixed_total_prior_original_weight (B:=E) hA P F hbranch hcover prior using 4
    ext i
    simp
  nlinarith

end ClusterFamily
end MinorFreeSpanners
