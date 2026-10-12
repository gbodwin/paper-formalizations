import MinorFreeSpanners.ExpandedOriginalRootBills
import MinorFreeSpanners.SelectedRootActualPayment
import MinorFreeSpanners.PartialResidualOwnership

/-! Actual high and weak bills after partial absorption. The high-root flag
is retained; only newly absorbed labels pay a touching-edge increment. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable
namespace ResidualOwnership
variable {I : Type*} [Fintype I] {H : SimpleGraph I} {roots : Finset I}

 theorem chosenFilled_biUnion (O : ResidualOwnership H roots)
    (Q : Finset (H.induce ((Finset.univ\roots : Finset I):Set I)).ConnectedComponent)
    (S : Finset {r // r∈roots}) :
    S.biUnion (O.chosenFilled Q)=S.image Subtype.val∪S.biUnion (O.chosenAbsorbed Q) := by
  classical
  ext i
  simp only [chosenFilled,Finset.mem_biUnion,Finset.mem_insert,Finset.mem_union,Finset.mem_image]
  aesop

end ResidualOwnership
namespace ClusterFamily
variable {I V : Type*} [Fintype I] [Fintype V]
variable {A B : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}

 theorem partial_absorption_bill_expansion (C : ClusterFamily (I:=I) A w D)
    {H : SimpleGraph I} {roots : Finset I} (O : ResidualOwnership H roots)
    (Q : Finset (H.induce ((Finset.univ\roots : Finset I):Set I)).ConnectedComponent)
    (high : Finset {r // r∈roots}) (a : ℝ)
    (hw : ∀ e∈B.edgeSet,0≤w e)
    (hpay : ∀ r,(∑ e∈C.touchingEdges B (O.chosenAbsorbed Q r),w e)≤a*(O.chosenAbsorbed Q r).card) :
    (∑ e∈C.touchingEdges B ((Finset.univ\high).biUnion (O.chosenFilled Q)),w e)+
      (∑ e∈C.markedEdges B (high.biUnion (O.chosenFilled Q)),w e)≤
        (∑ e∈C.touchingEdges B ((Finset.univ\high).image Subtype.val),w e)+
        (∑ e∈C.markedEdges B (high.image Subtype.val),w e)+
        ∑ r,a*(O.chosenAbsorbed Q r).card := by
  classical
  have hp (S : Finset {r // r∈roots}) :
      (∑ e∈C.touchingEdges B (S.biUnion (O.chosenAbsorbed Q)),w e)≤
        ∑ r∈S,a*(O.chosenAbsorbed Q r).card := by
    rw [C.touching_edges_biUnion]
    convert (finite_union_weight_le S (fun r => C.touchingEdges B (O.chosenAbsorbed Q r)) w
      (fun _ _ e he => hw e (mem_edgeFinset.mp (Finset.mem_filter.mp he).1))).trans
      (Finset.sum_le_sum (fun r _ => hpay r)) using 1
    congr 1
    ext e
    simp
  rw [O.chosenFilled_biUnion Q (Finset.univ\high),O.chosenFilled_biUnion Q high]
  have hwk := C.expanded_touching_weight_le ((Finset.univ\high).image Subtype.val)
    ((Finset.univ\high).biUnion (O.chosenAbsorbed Q)) hw
  have hhi := C.expanded_marked_weight_le (high.image Subtype.val)
    (high.biUnion (O.chosenAbsorbed Q)) hw
  have hs := Finset.sum_sdiff (f:=fun r => a*(O.chosenAbsorbed Q r).card) (Finset.subset_univ high)
  linarith [hp (Finset.univ\high),hp high]

end ClusterFamily
end MinorFreeSpanners
