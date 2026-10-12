import MinorFreeSpanners.ConstructedOriginalDiameterPhase
import MinorFreeSpanners.RetainedMetricFamily

/-! Construct the original-diameter heavy phase and its covering next family
from the actual expanded-root bill and literal prior connector history. The
ownership, segmentation, heavy owners, metric witnesses and retained credit
are all produced internally and share the same exact resource ledger. -/
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
variable {d credit : SelectedResidualIndex P → ℝ} {M L c b a : ℝ}
variable {spare reserve : {r // r∈(selectedRoots P)} → ℝ} {N : ℕ}


attribute [-instance] instDecidableEqSum in
 theorem exists_constructed_retained_credit_family (hcover : ∀ x,∃ i,x∈C.branch i) (hunit : ∀ e∈T.edgeSet,w e=1) (hE : E≤G)
    (hforest : H.IsAcyclic) (hconn : ConnectedWithin H Finset.univ)
    (hP : P.Nonempty) (Horiginal : SimpleGraph I) (hOriginal : Horiginal.IsAcyclic)
    (hres : ∀ i j : {i // i∉P.biUnion id},H.Adj (Sum.inr i) (Sum.inr j) ↔ Horiginal.Adj i.val j.val)
    (originalD : I → ℝ) (radius : {S // S∈P} → ℝ)
    (hmixed : (fun i => d i+1)=mixedEffectiveDiameter originalD radius)
    (W U : Finset I) (high : Finset {S // S∈P})
    (hRW : Finset.univ\P.biUnion id⊆W) (hRU : Disjoint (Finset.univ\P.biUnion id) U)
    (hmax : ∀ S : Finset I,S⊆W → Disjoint S U →
      ¬C.ShortCycleCore Horiginal originalD L E S ∧ ¬C.FourArmCore Horiginal originalD L E S)
    (edgeMax : ℝ) (future : {r // r∈(selectedRoots P)} → ℝ)
    (hM : 0≤M) (hL : 0<L) (hK : 1≤2*L+M) (hMax : 0≤edgeMax) (hc : 0≤c) (ha : 0≤a)
    (hroot0 : ∀ r∈(selectedRoots P),0≤d r) (hd0 : ∀ i∈W,0≤originalD i+1) (hdD : ∀ i∈W,originalD i≤D)
    (hd : ∀ i∉(selectedRoots P),1≤d i) (hdM : ∀ i∉(selectedRoots P),d i+1≤M)
    (hdeg2 : ∀ i∉(selectedRoots P),((H.neighborFinset i)\(selectedRoots P)).card≤2)
    (hm : ∀ t : (H.induce ((Finset.univ\(selectedRoots P) : Finset (SelectedResidualIndex P)):Set (SelectedResidualIndex P))).ConnectedComponent,
      L≤∑ i∈ResidualComponents.block H (Finset.univ\(selectedRoots P)) t,(d i+1))
    (hdiam : ∀ i x,x∈(C.selectedResidual hA P F hbranch).branch i → ∀ y,y∈(C.selectedResidual hA P F hbranch).branch i →
      ∃ q : G.Walk x y,(∀ z∈q.support,z∈(C.selectedResidual hA P F hbranch).branch i) ∧ walkWeight w q≤d i)
    (hcredit : ∀ i∉(selectedRoots P),c*d i≤credit i) (hbase : ∀ i∉(selectedRoots P),c*b≤credit i)
    (hcredit0 : ∀ i,0≤credit i)
    (hrootcredit : ∀ r,c*d r.val+spare r≤credit r.val)
    (hweight : ∀ e∈E.edgeSet,w e≤edgeMax)
    (hfuture : ∀ r,future r≤reserve r)
    (hbudget : ∀ r,r.val∈highRootEligible P high → 2*c*edgeMax+2*(N:ℝ)*a+future r≤reserve r)
    (hsize : 2*(2*L+M)≤N*b) (hhalf : 2*a≤c*b)
    (hdonor : 2*(N:ℝ)*a≤c*L/4) (hrootbudget : ∀ r,5*(N:ℝ)*a+reserve r≤spare r)
    (hcost : (N+1:ℕ)*a≤c*b/2)
    (q : ℕ) (hqa : (q:ℝ)*edgeMax≤a)
    (hdeg : ∀ i,i∉P.biUnion id → (C.graph E).degree i≤q)
    (hw0 : ∀ e∈E.edgeSet,0≤w e)
    (hloop : ∀ i x,x∈C.branch i → ∀ y,y∈C.branch i → ¬E.Adj x y)
    (hsingle : ∀ i j x,x∈C.branch i → ∀ y,y∈C.branch j →
      ∀ u,u∈C.branch i → ∀ v,v∈C.branch j → E.Adj x y → E.Adj u v → s(x,y)=s(u,v))
    (priorEdges : Finset (Sym2 V))
    (hinternal : ∀ e∈priorEdges,∃ g x y,x∈F.branch g ∧ y∈F.branch g ∧ e=s(x,y))
    (initial rootBound baseline : ℝ)
    (hroot : ∀ r : {r // r∈selectedRoots P},d r.val≤rootBound)
    (hb : 0≤b) (hbaseline : 0≤baseline) (hblockbase : baseline≤L-1)
    (hfuture0 : ∀ r,0≤future r)
    (hrootbase : ∀ r : {r // r∈selectedRoots P},c*baseline≤c*d r.val+future r)
    (hprior : (∑ e∈C.touchingEdges E ((Finset.univ\high).biUnion Subtype.val),w e)+
      (∑ e∈C.markedEdges E (high.biUnion Subtype.val),w e)+
      (∑ i,credit i)≤ initial+c*(∑ e∈priorEdges,w e)) :
    ∃ O : ResidualOwnership H (selectedRoots P),
    ∃ Q : (r : {r // r∈selectedRoots P}) → RootedPathAssemblyResult (C.selectedResidual hA P F hbranch)
      le_rfl hT H hH (Finset.univ\selectedRoots P) r.val (O.components r) O.port
      (fun i => d i+1) credit M L c b a (spare r) (reserve r) N,
    let active := (C.selectedResidual hA P F hbranch).heavyAttachmentBlocks E
      (smallBlocks O Q) (allPaidLabels O Q∪weakRootPrior P high)
    ∃ owner : {S // S∈active} → {r // r∈selectedRoots P},
    ∃ radius : {r // r∈selectedRoots P}⊕{S // S∈leftovers O Q\active} → ℝ,
    ∃ keep : {r // r∈selectedRoots P}⊕{S // S∈leftovers O Q\active} → ℝ,
    ∃ next : ClusterFamily (I:={r // r∈selectedRoots P}⊕{S // S∈leftovers O Q\active}) G w
      (max (rootBound+4*(2*L+M)+2*edgeMax) (2*L+M-1)),
      (∀ j,next.branch j={x | ∃ i∈retainedCarrier O Q active owner j,
        x∈(C.selectedResidual hA P F hbranch).branch i}) ∧
      (∀ x,∃ j,x∈next.branch j) ∧
      (∀ j,∀ x∈next.branch j,∀ y∈next.branch j,
        ∃ p : G.Walk x y,(∀ z∈p.support,z∈next.branch j) ∧ walkWeight w p≤radius j) ∧
      (∀ e∈priorEdges∪retainedConnectorPool O Q active owner,
        ∃ j x y,x∈next.branch j ∧ y∈next.branch j ∧ e=s(x,y)) ∧
      Disjoint priorEdges (retainedConnectorPool O Q active owner) ∧
      (∀ j,c*max (radius j) baseline≤keep j) ∧ (∀ j,0≤keep j) ∧
      (∑ e∈E.edgeFinset,w e)+(∑ j,keep j)≤
            initial+c*(∑ e∈priorEdges∪retainedConnectorPool O Q active owner,w e) := by
  have hprevious : selectedRoots P\highRootEligible P high⊆weakRootPrior P high := by
    simpa only [Finset.subset_iff,Finset.mem_sdiff] using
      (selected_roots_prior_or_eligible P high).le
  obtain ⟨_,O,Q,hphase⟩ := exists_original_diameter_mixed_phase_exact C hA P F hbranch hcover hunit hE
    hforest hconn hP Horiginal hOriginal hres originalD radius hmixed W U
    (weakRootPrior P high) (highRootEligible P high) hprevious hRW hRU hmax edgeMax future
    hM hL hK hMax hc ha hroot0 hd0 hdD hd hdM hdeg2 hm hdiam hcredit hbase hcredit0 hrootcredit
    hweight hfuture hbudget hsize hhalf hdonor hrootbudget hcost q hqa hdeg hw0 hloop hsingle
  refine ⟨O,Q,?_⟩
  exact retained_metric_family_from_expanded_bills C hA P F hbranch O Q hcover priorEdges hinternal
    high edgeMax initial rootBound baseline future hroot hc hb hbaseline hblockbase hfuture0 hrootbase hprior hphase

end AssembledPathFamilies
end MinorFreeSpanners
