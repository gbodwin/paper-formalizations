import MinorFreeSpanners.MixedAssembledWeightPayment
import MinorFreeSpanners.AssembledPaidHeavyPhase

/-! The mixed-root phase spends actual host-edge weight using pre-merge
original degrees, while retaining its same constructed carriers and metric
credit. No single-edge hypothesis is imposed on collapsed large roots. -/
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
variable {spare reserve : {r // r∈(selectedRoots P)} → ℝ} {N : ℕ}


attribute [-instance] instDecidableEqSum in
 theorem mixed_paid_full_heavy_phase
    (Q : (r : {r // r∈(selectedRoots P)}) → RootedPathAssemblyResult (C.selectedResidual hA P F hbranch) le_rfl hT H hH
    (Finset.univ\(selectedRoots P)) r.val (O.components r) O.port (fun i => d i+1) credit M L c b a (spare r) (reserve r) N)
    (hcover : ∀ x,∃ i,x∈C.branch i) (hunit : ∀ e∈T.edgeSet,w e=1) (hE : E≤G)
    (hforest : H.IsAcyclic) (W U : Finset (SelectedResidualIndex P))
    (hRW : Finset.univ\(selectedRoots P)⊆W) (hRU : Disjoint (Finset.univ\(selectedRoots P)) U)
    (hmax : ∀ S : Finset (SelectedResidualIndex P),S⊆W → Disjoint S U →
      ¬(C.selectedResidual hA P F hbranch).ShortCycleCore H d L E S ∧ ¬(C.selectedResidual hA P F hbranch).FourArmCore H d L E S)
    (edgeMax : ℝ) (future : {r // r∈(selectedRoots P)} → ℝ)
    (hL : 0<L) (hK : 1≤2*L+M) (hMax : 0≤edgeMax) (hc : 0≤c) (ha : 0≤a)
    (hroot0 : ∀ r∈(selectedRoots P),0≤d r) (hd0 : ∀ i∈W,0≤d i+1) (hdD : ∀ i∈W,d i≤max D D₁)
    (hd : ∀ i∉(selectedRoots P),0≤d i)
    (hdiam : ∀ i x,x∈(C.selectedResidual hA P F hbranch).branch i → ∀ y,y∈(C.selectedResidual hA P F hbranch).branch i →
      ∃ q : G.Walk x y,(∀ z∈q.support,z∈(C.selectedResidual hA P F hbranch).branch i) ∧ walkWeight w q≤d i)
    (hcredit : ∀ i∉(selectedRoots P),c*d i≤credit i) (hbase : ∀ i∉(selectedRoots P),a≤credit i)
    (hcredit0 : ∀ i,0≤credit i)
    (hrootcredit : ∀ r,c*d r.val+spare r≤credit r.val)
    (hweight : ∀ e∈E.edgeSet,w e≤edgeMax)
    (hbudget : ∀ r,2*c*edgeMax+2*(N:ℝ)*a+future r≤reserve r)
    (q : ℕ) (hqa : (q:ℝ)*edgeMax≤a)
    (hdeg : ∀ i,i∉P.biUnion id → (C.graph E).degree i≤q)
    (hw0 : ∀ e∈E.edgeSet,0≤w e)
    (hloop : ∀ i x,x∈C.branch i → ∀ y,y∈C.branch i → ¬E.Adj x y)
    (hsingle : ∀ i j x,x∈C.branch i → ∀ y,y∈C.branch j →
      ∀ u,u∈C.branch i → ∀ v,v∈C.branch j → E.Adj x y → E.Adj u v → s(x,y)=s(u,v)) :
    PaidHeavyPhaseOutput O Q E edgeMax future := by
  classical
  obtain ⟨owner,rootRadius,blockRadius,hedges,hempty,hne,hdis,hcarrierCover,hrr,hbr,hwalk,hledger⟩ :=
    full_heavy_phase O Q hunit hE hforest W U hRW hRU hmax edgeMax future
      hL hK hMax hc ha hroot0 hd0 hdD hd hdiam hcredit hbase hcredit0 hrootcredit hweight hbudget
  let active := (C.selectedResidual hA P F hbranch).heavyAttachmentBlocks E (smallBlocks O Q) (allPaidLabels O Q)
  have hactive : active⊆smallBlocks O Q := Finset.filter_subset _ _
  have hpaid := mixed_original_weight_payment C hA P F hbranch O Q hcover hE
    active hactive owner hempty q edgeMax hMax ha hqa hdeg hw0 hweight hloop hsingle
  refine ⟨owner,rootRadius,blockRadius,hedges,hempty,hne,hdis,hcarrierCover,hrr,hbr,hwalk,?_⟩
  have hroot :
      (∑ r,(rootSpent O Q r+c*rootRadius r+a*(assignedBlockUnion active owner r).card+future r))=
      (∑ r,(rootSpent O Q r+a*(assignedBlockUnion active owner r).card))+
        ∑ r,(c*rootRadius r+future r) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r _
    ring
  have hblock :
      (∑ S : {S // S∈leftovers O Q\active},
        (c*blockRadius S+(if N<S.val.card then a*S.val.card+c*b/2 else 0)))=
      (∑ S : {S // S∈leftovers O Q\active},(if N<S.val.card then a*S.val.card else 0))+
        ∑ S : {S // S∈leftovers O Q\active},(c*blockRadius S+(if N<S.val.card then c*b/2 else 0)) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro S _
    split_ifs <;> ring
  rw [hroot,hblock] at hledger
  linarith

end AssembledPathFamilies
end MinorFreeSpanners
