import MinorFreeSpanners.AssembledOriginalWeightPayment
import MinorFreeSpanners.MixedOriginalEdgeTransport
import MinorFreeSpanners.MixedSmallAbsorptionPhase

/-! Actual heavy-edge payment for a mixed family uses the original pre-merge
cluster degree and edge uniqueness. Collapsed large roots may conceal many
parallel original incidences; none is discarded or counted by quotient degree. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable
namespace AssembledPathFamilies
variable {I V : Type*} [Fintype I] [Fintype V]
variable {A T E G : SimpleGraph V} {w : Sym2 V → ℝ} {D D₁ : ℝ}
variable (C : ClusterFamily (I:=I) A w D) (hA : A≤G) {hT : T≤G}
variable (P : Finset (Finset I)) (F : ClusterFamily (I:={S // S∈P}) G w D₁)
variable (hbranch : ∀ S,F.branch S={x | ∃ i∈S.val,x∈C.branch i})
variable {H : SimpleGraph (SelectedResidualIndex P)} {hH : H≤(C.selectedResidual hA P F hbranch).graph T}
variable (O : ResidualOwnership H (selectedRoots P))
variable {d credit : SelectedResidualIndex P → ℝ} {M L c b a : ℝ}
variable {spare future : {r // r∈(selectedRoots P)} → ℝ} {N : ℕ}


attribute [-instance] instDecidableEqSum in
 theorem mixed_original_weight_payment
    (Q : (r : {r // r∈(selectedRoots P)}) → RootedPathAssemblyResult (C.selectedResidual hA P F hbranch) le_rfl hT H hH
    (Finset.univ\(selectedRoots P)) r.val (O.components r) O.port d credit M L c b a (spare r) (future r) N)
    (hcover : ∀ x,∃ i,x∈C.branch i) (hE : E≤G)
    (active : Finset (Finset (SelectedResidualIndex P))) (hactive : active⊆smallBlocks O Q)
    (owner : {S // S∈active} → {r // r∈(selectedRoots P)})
    (hempty : ∀ S∈leftovers O Q,S∉active → (C.selectedResidual hA P F hbranch).unpaidTouchingEdges E S (allPaidLabels O Q)=∅)
    (q : ℕ) (edgeMax : ℝ) (hMax : 0≤edgeMax) (ha : 0≤a) (hqa : (q:ℝ)*edgeMax≤a)
    (hdeg : ∀ i,i∉P.biUnion id → (C.graph E).degree i≤q)
    (hw0 : ∀ e∈E.edgeSet,0≤w e) (hw : ∀ e∈E.edgeSet,w e≤edgeMax)
    (hloop : ∀ i x,x∈C.branch i → ∀ y,y∈C.branch i → ¬E.Adj x y)
    (hsingle : ∀ i j x,x∈C.branch i → ∀ y,y∈C.branch j →
      ∀ u,u∈C.branch i → ∀ v,v∈C.branch j → E.Adj x y → E.Adj u v → s(x,y)=s(u,v)) :
    (∑ e∈(C.selectedResidual hA P F hbranch).touchingEdges E (Finset.univ\(selectedRoots P)),w e)≤
      (∑ r,(rootSpent O Q r+a*(assignedBlockUnion active owner r).card))+
      ∑ S : {S // S∈leftovers O Q\active},(if N<S.val.card then a*S.val.card else 0) := by
  classical
  have hfree : ∀ t : {S // S∈P},Sum.inl t∉chargeLabels O Q active owner := by
    intro t ht
    exact (Finset.mem_sdiff.mp (charge_subset_residual O Q active
      (hactive.trans (smallBlocks_subset O Q)) owner ht)).2 (by simp [selectedRoots])
  have hsub := residual_touching_subset_charge O Q E active owner hempty
  have hh := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun e he _ => hw0 e (mem_edgeFinset.mp (Finset.mem_filter.mp he).1))
  have hmixed := C.mixed_touching_weight_le hA hE P F hbranch hcover
    (chargeLabels O Q active owner) hfree q edgeMax hMax hdeg hw hloop hsingle
  have hpaid := (hh.trans hmixed).trans
    (mul_le_mul_of_nonneg_right hqa (Nat.cast_nonneg _))
  have hb := hpaid.trans (charge_budget O Q active owner ha)
  simpa only [large_allocation_eq_inactive O Q active hactive] using hb

end AssembledPathFamilies
end MinorFreeSpanners
