import MinorFreeSpanners.AssembledLargeBlockCredit
import MinorFreeSpanners.AssembledResidualExclusion
import MinorFreeSpanners.ActualUnpaidHeavyAbsorption

/-! The previously constructed root fibers themselves supply every carrier,
path, spent-credit ledger and residual-edge exclusion used in heavy absorption.
The original forest, credit/diameter invariants, core maximality and common
numerical budget conditions remain explicit. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable
namespace AssembledPathFamilies
variable {I V : Type*} [Fintype I] [Fintype V] {A T E G : SimpleGraph V} {w : Sym2 V → ℝ} {D₀ : ℝ}
variable {C : ClusterFamily (I:=I) A w D₀} {hA : A≤G} {hT : T≤G}
variable {H : SimpleGraph I} {hH : H≤C.graph T} {roots : Finset I}
variable (O : ResidualOwnership H roots)
variable {d credit : I → ℝ} {M L c b a : ℝ} {spare reserve : {r // r∈roots} → ℝ} {N : ℕ}
variable (Q : (r : {r // r∈roots}) → RootedPathAssemblyResult C hA hT H hH
    (Finset.univ\roots) r.val (O.components r) O.port (fun i => d i+1) credit M L c b a (spare r) (reserve r) N)

 theorem small_heavy_output (hunit : ∀ e∈T.edgeSet,w e=1) (hE : E≤G)
    (hforest : H.IsAcyclic) (W U : Finset I)
    (hRW : Finset.univ\roots⊆W) (hRU : Disjoint (Finset.univ\roots) U)
    (hmax : ∀ S : Finset I,S⊆W → Disjoint S U →
      ¬C.ShortCycleCore H d L E S ∧ ¬C.FourArmCore H d L E S)
    (edgeMax : ℝ) (future : {r // r∈roots} → ℝ)
    (hL : 0<L) (hK : 1≤2*L+M) (hMax : 0≤edgeMax) (hc : 0≤c) (ha : 0≤a)
    (hroot0 : ∀ r∈roots,0≤d r) (hd0 : ∀ i∈W,0≤d i+1) (hdD : ∀ i∈W,d i≤D₀)
    (hd : ∀ i∉roots,0≤d i)
    (hdiam : ∀ i x,x∈C.branch i → ∀ y,y∈C.branch i →
      ∃ q : A.Walk x y,(∀ z∈q.support,z∈C.branch i) ∧ walkWeight w q≤d i)
    (hcredit : ∀ i∉roots,c*d i≤credit i) (hbase : ∀ i∉roots,a≤credit i)
    (hcredit0 : ∀ i,0≤credit i)
    (hrootcredit : ∀ r,c*d r.val+spare r≤credit r.val)
    (hweight : ∀ e∈E.edgeSet,w e≤edgeMax)
    (hbudget : ∀ r,2*c*edgeMax+2*(N:ℝ)*a+future r≤reserve r) :
    let active := C.heavyAttachmentBlocks E (smallBlocks O Q) (allPaidLabels O Q)
    ∃ owner : {S // S∈active} → {r // r∈roots},∃ newRadius : {r // r∈roots} → ℝ,
      (∀ S,∃ x y,(∃ i∈rootCarrier O Q (owner S),x∈C.branch i) ∧
        (∃ i∈S.val,y∈C.branch i) ∧ s(x,y)∈C.unpaidTouchingEdges E S.val (allPaidLabels O Q)) ∧
      (∀ S∈smallBlocks O Q,S∉active → C.unpaidTouchingEdges E S (allPaidLabels O Q)=∅) ∧
      (∀ r,(Q r).radius≤newRadius r ∧ newRadius r≤(Q r).radius+2*edgeMax+2*(2*L+M-1)) ∧
      let filled := fun r => rootCarrier O Q r∪assignedBlockUnion active owner r
      (∀ r,∀ x∈{x | ∃ i∈filled r,x∈C.branch i},∀ y∈{x | ∃ i∈filled r,x∈C.branch i},
        ∃ p : G.Walk x y,(∀ z∈p.support,∃ i∈filled r,z∈C.branch i) ∧ walkWeight w p≤newRadius r) ∧
      (∀ r,rootSpent O Q r+c*newRadius r+a*(assignedBlockUnion active owner r).card+future r≤
        (∑ i∈filled r,credit i)+c*(∑ e∈C.connectorEdges hA hT (C.graph T) le_rfl (filled r),w e)) := by
  classical
  have hpart := full_partition O Q
  have hsub : ∀ S∈smallBlocks O Q,S⊆Finset.univ\roots :=
    fun S hS => leftover_subset O Q (smallBlocks_subset O Q hS)
  have hUR : (smallBlocks O Q).biUnion id⊆Finset.univ\roots := by
    intro i hi
    obtain ⟨S,hS,hi⟩ := Finset.mem_biUnion.mp hi
    exact hsub S hS hi
  have hUP : (smallBlocks O Q).biUnion id⊆(leftovers O Q).biUnion id := by
    intro i hi
    obtain ⟨S,hS,hi⟩ := Finset.mem_biUnion.mp hi
    exact Finset.mem_biUnion.mpr ⟨S,smallBlocks_subset O Q hS,hi⟩
  obtain ⟨owner,hedges,hempty,_,_,_,radius,hr,hwalk,hpay,_⟩ :=
    actual_unpaid_heavy_absorption C hA hT hE hunit H hH (smallBlocks O Q) (Finset.univ\roots)
      (allPaidLabels O Q) roots (rootCarrier O Q) (fun r => (Q r).rootGraph)
      (fun r => (Q r).rootGraph_sub) (fun i => d i+1) credit (fun r => (Q r).radius)
      reserve (rootSpent O Q) future L (2*L+M) edgeMax c a N
      (fun r => by have hh := (Q r).radius_lower;have hz := hroot0 r.val r.property;linarith)
      hK hMax hc ha hpart.1 hpart.2.1 (fun r => (hpart.2.2.2.2.1 r).mono_right hUP)
      (fun S hS U hU => hpart.2.2.2.1 S (smallBlocks_subset O Q hS) U (smallBlocks_subset O Q hU))
      (by
        intro S hS
        obtain ⟨x,y,p,hp,he,hlo,hhi⟩ := leftover_good O Q (smallBlocks_subset O Q hS)
        exact ⟨x,y,p,hp,he,hlo,hhi.le⟩)
      (fun S hS => (Finset.mem_filter.mp hS).2)
      (fun i hi => by have hh := hd i (Finset.mem_sdiff.mp (hUR hi)).2;linarith)
      (by simpa only [add_sub_cancel_right] using hdiam)
      (by simpa only [add_sub_cancel_right] using fun i hi => hcredit i (Finset.mem_sdiff.mp (hUR hi)).2)
      (fun i hi => hbase i (Finset.mem_sdiff.mp (hUR hi)).2) hcredit0
      (fun r => Finset.mem_insert_self _ _) hweight hsub (old_label_cover O Q)
      (no_unpaid_edge O Q hforest W U hRW hRU hmax hL hd0 hdD)
      (fun r => (Q r).root_walks)
      (fun r => root_ledger O Q r (by simpa only [add_sub_cancel_right] using hrootcredit r)) hbudget
  exact ⟨owner,radius,hedges,hempty,hr,hwalk,hpay⟩

end AssembledPathFamilies
end MinorFreeSpanners
