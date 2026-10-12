import MinorFreeSpanners.SelectedRootCreditTransfer
import MinorFreeSpanners.SelectedRootActualPayment
import MinorFreeSpanners.SelectedRootPriorLabels

/-! Derive the exact earlier certificate consumed by the mixed total-payment
join from the high-degree marked-edge bill and each weak root's actual touching
bill. Retained mixed credit is constructed from actual root credit and unchanged
residual credit; neither a paid scalar nor an unrelated credit ledger is supplied. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable
namespace ClusterFamily
variable {I V : Type*} [Fintype I] [Fintype V]
variable {A T E G : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}

 theorem prior_credit_from_phase_bills (C : ClusterFamily (I:=I) A w D)
    (hA : A≤G) (hT : T≤G) (P : Finset (Finset I))
    (hP : ∀ S U,S∈P → U∈P → S≠U → Disjoint S U)
    (high : Finset {S // S∈P}) (H : {S // S∈P} → SimpleGraph I)
    (hH : ∀ S,H S≤C.graph T) (old : I → ℝ) (keep : {S // S∈P} → ℝ)
    (c : ℝ) (hc : 0≤c) (hwT : ∀ e∈T.edgeSet,0≤w e) (hwE : ∀ e∈E.edgeSet,0≤w e)
    (hhigh : (∑ e∈C.markedEdges E (high.biUnion Subtype.val),w e)+(∑ S∈high,keep S)≤
      ∑ S∈high,∑ i∈S.val,old i)
    (hweak : ∀ S,S∉high → (∑ e∈C.touchingEdges E S.val,w e)+keep S≤
      (∑ i∈S.val,old i)+c*(∑ e∈C.connectorEdges hA hT (H S) (hH S) S.val,w e)) :
    (∑ e∈C.touchingEdges E (originalMixedLabels P (weakRootPrior P high)),w e)+
      (∑ e∈C.markedEdges E (P.biUnion id\originalMixedLabels P (weakRootPrior P high)),w e)+
      (∑ i,selectedResidualCredit P keep old i)≤
        (∑ i,old i)+c*(∑ e∈C.connectorPool hA hT H hH Subtype.val,w e) := by
  classical
  have hp := C.selected_root_actual_payment hA hT high Subtype.val
    (fun S U hne => hP S.val U.val S.property U.property (fun he => hne (Subtype.ext he)))
    H hH old keep c hc hwT hwE hhigh hweak
  rw [selected_group_union] at hp
  rw [selected_high_labels P hP high,original_weakRootPrior]
  apply selected_root_credit_transfer P keep old
  calc
    _ = (∑ e∈C.markedEdges E (high.biUnion Subtype.val),w e)+
        (∑ e∈C.touchingEdges E ((Finset.univ\high).biUnion Subtype.val),w e)+(∑ S,keep S) := by ring
    _ ≤ _ := by
      convert hp using 4
      ext e
      simp [touchingEdges]

end ClusterFamily
end MinorFreeSpanners
