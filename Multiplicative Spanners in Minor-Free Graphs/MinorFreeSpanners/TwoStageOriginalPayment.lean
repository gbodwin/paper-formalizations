import MinorFreeSpanners.MixedConnectorFreshness
import MinorFreeSpanners.PriorPhaseOriginalPartition

/-! The actual original-edge partition joins an earlier selected-root payment
certificate to the later mixed residual bill. The two actual connector pools
are disjoint by branch containment, so their union is counted exactly once.
The earlier spending-and-retained-credit certificate is an explicit premise;
this lemma does not manufacture it from a bare scalar reserve. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable
namespace ClusterFamily
variable {I V J : Type*} [Fintype I] [Fintype V] [Fintype J]
variable {A T E G : SimpleGraph V} {w : Sym2 V → ℝ} {D D₁ : ℝ}

attribute [-instance] instDecidableEqSum in
 theorem two_stage_original_payment (C : ClusterFamily (I:=I) A w D)
    (hA : A≤G) (hT : T≤G) (P : Finset (Finset I))
    (F : ClusterFamily (I:={S // S∈P}) G w D₁)
    (hbranch : ∀ S,F.branch S={x | ∃ i∈S.val,x∈C.branch i})
    (hcover : ∀ x,∃ i,x∈C.branch i)
    (oldH : {S // S∈P} → SimpleGraph I) (holdH : ∀ S,oldH S≤C.graph T)
    (newH : J → SimpleGraph (SelectedResidualIndex P))
    (hnewH : ∀ j,newH j≤(C.selectedResidual hA P F hbranch).graph T)
    (carrier : J → Finset (SelectedResidualIndex P))
    (prior : Finset (SelectedResidualIndex P)) (credit : SelectedResidualIndex P → ℝ)
    (initial future c : ℝ)
    (hprior : (∑ e∈C.touchingEdges E (originalMixedLabels P prior),w e)+
      (∑ e∈C.markedEdges E (P.biUnion id\originalMixedLabels P prior),w e)+
      (∑ i,credit i)≤ initial+c*(∑ e∈C.connectorPool hA hT oldH holdH Subtype.val,w e))
    (hresidual : (∑ e∈(C.selectedResidual hA P F hbranch).unpaidTouchingEdges E
      (Finset.univ\selectedRoots P) prior,w e)+future≤(∑ i,credit i)+
      c*(∑ e∈(C.selectedResidual hA P F hbranch).connectorPool le_rfl hT newH hnewH carrier,w e)) :
    (∑ e∈E.edgeFinset,w e)+future≤ initial+
      c*(∑ e∈C.connectorPool hA hT oldH holdH Subtype.val ∪
        (C.selectedResidual hA P F hbranch).connectorPool le_rfl hT newH hnewH carrier,w e) := by
  classical
  have hd := C.mixed_connectorPool_disjoint_prior hA hT P F hbranch oldH holdH newH hnewH carrier
  rw [Finset.sum_union hd]
  have he : (∑ e∈E.edgeFinset,w e)=(∑ e∈C.touchingEdges E (originalMixedLabels P prior),w e)+
      (∑ e∈C.markedEdges E (P.biUnion id\originalMixedLabels P prior),w e)+
      ∑ e∈(C.selectedResidual hA P F hbranch).unpaidTouchingEdges E
        (Finset.univ\selectedRoots P) prior,w e := by
    convert C.mixed_total_prior_original_weight (B:=E) hA P F hbranch hcover prior using 4
    ext i
    simp
  nlinarith

 theorem two_stage_connector_resource_bound (C : ClusterFamily (I:=I) A w D)
    (hA : A≤G) (hT : T≤G) (P : Finset (Finset I))
    (F : ClusterFamily (I:={S // S∈P}) G w D₁)
    (hbranch : ∀ S,F.branch S={x | ∃ i∈S.val,x∈C.branch i})
    (oldH : {S // S∈P} → SimpleGraph I) (holdH : ∀ S,oldH S≤C.graph T)
    (newH : J → SimpleGraph (SelectedResidualIndex P))
    (hnewH : ∀ j,newH j≤(C.selectedResidual hA P F hbranch).graph T)
    (carrier : J → Finset (SelectedResidualIndex P))
    (hw : ∀ e∈T.edgeSet,0≤w e) :
    (∑ e∈C.connectorPool hA hT oldH holdH Subtype.val,w e)+
      (∑ e∈(C.selectedResidual hA P F hbranch).connectorPool le_rfl hT newH hnewH carrier,w e)≤
        ∑ e∈T.edgeFinset,w e := by
  classical
  rw [←Finset.sum_union (C.mixed_connectorPool_disjoint_prior hA hT P F hbranch oldH holdH newH hnewH carrier)]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro e he
    rcases Finset.mem_union.mp he with he|he
    · exact mem_edgeFinset.mpr (C.connectorPool_mem hA hT oldH holdH Subtype.val he)
    · exact mem_edgeFinset.mpr ((C.selectedResidual hA P F hbranch).connectorPool_mem le_rfl hT newH hnewH carrier he)
  · intro e he _
    exact hw e (mem_edgeFinset.mp he)

end ClusterFamily
end MinorFreeSpanners
