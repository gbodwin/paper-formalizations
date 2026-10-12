import MinorFreeSpanners.PartialAbsorptionBillExpansion
import MinorFreeSpanners.ExactConnectorPooling

/-! Pool the actual new root metric/future credits and preserve every unabsorbed
old credit. The previous phase bill is extended with the same fresh connector
union, rather than charging the spanning-tree resource a second time. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable
namespace ClusterFamily
variable {I V : Type*} [Fintype I] [Fintype V]
variable {A B T G : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}

 theorem partial_absorption_credit_ledger (C : ClusterFamily (I:=I) A w D)
    (hA : A≤G) (hT : T≤G) {H : SimpleGraph I} {roots : Finset I}
    (O : ResidualOwnership H roots)
    (Q : Finset (H.induce ((Finset.univ\roots : Finset I):Set I)).ConnectedComponent)
    (high : Finset {r // r∈roots}) (old : I → ℝ) (keep : {r // r∈roots} → ℝ)
    (c a resource : ℝ) (hw : ∀ e∈B.edgeSet,0≤w e)
    (htouch : ∀ r,(∑ e∈C.touchingEdges B (O.chosenAbsorbed Q r),w e)≤a*(O.chosenAbsorbed Q r).card)
    (hlocal : ∀ r,a*(O.chosenAbsorbed Q r).card+keep r≤old r.val+
      (∑ i∈O.chosenAbsorbed Q r,old i)+
      c*(∑ e∈C.connectorEdges hA hT (C.graph T) le_rfl (O.chosenFilled Q r),w e))
    (hprior : (∑ e∈C.touchingEdges B ((Finset.univ\high).image Subtype.val),w e)+
      (∑ e∈C.markedEdges B (high.image Subtype.val),w e)+(∑ i,old i)≤resource) :
    (∑ e∈C.touchingEdges B ((Finset.univ\high).biUnion (O.chosenFilled Q)),w e)+
      (∑ e∈C.markedEdges B (high.biUnion (O.chosenFilled Q)),w e)+(∑ r,keep r)+
      (∑ i∈Finset.univ\Finset.univ.biUnion (O.chosenFilled Q),old i)≤
        resource+c*(∑ e∈C.connectorPool hA hT (fun _ => C.graph T) (fun _ => le_rfl)
          (O.chosenFilled Q),w e) := by
  classical
  have hpaid := C.disjoint_credit_pooling_exact hA hT (fun _ => C.graph T) (fun _ => le_rfl)
    (O.chosenFilled Q) (O.chosenFilled_disjoint Q) old
    (fun r => a*(O.chosenAbsorbed Q r).card+keep r) c (by
      intro r
      have hn : r.val∉O.chosenAbsorbed Q r := fun h => O.root_not_absorbed r r (O.chosenAbsorbed_subset Q r h)
      simpa only [ResidualOwnership.chosenFilled,Finset.sum_insert hn] using hlocal r)
  rw [Finset.sum_add_distrib] at hpaid
  have hsplit := Finset.sum_sdiff (f:=old) (Finset.subset_univ (Finset.univ.biUnion (O.chosenFilled Q)))
  have hbill := C.partial_absorption_bill_expansion O Q high a hw htouch
  linarith

end ClusterFamily
end MinorFreeSpanners
