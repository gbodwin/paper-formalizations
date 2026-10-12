import MinorFreeSpanners.ExpandedRootCreditInputs
import MinorFreeSpanners.FiniteRetainedPhaseOutput

/-! Consume one actual paid short-absorption result all the way through the
long heavy phase. Its exact original edge bill, literal prior connector union,
residual tree, component mass, degree bounds and retained root credit are joined
on the same witnesses. No second short absorption or prior bill is assumed. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset AssembledPathFamilies
attribute [local instance] Classical.propDecidable

attribute [-instance] instDecidableEqSum in
 theorem retained_family_after_paid_short {I V : Type*} [Fintype I] [Fintype V]
    {A B T G : SimpleGraph V} {w : Sym2 V → ℝ} {D E : ℝ}
    (C : ClusterFamily (I:=I) A w D) (hA : A≤G) (hB : B≤G) (hT : T≤G)
    (hcover : ∀ x,∃ i,x∈C.branch i) (hunit : ∀ e∈T.edgeSet,w e=1)
    (P : Finset (Finset I)) (hP : P.Nonempty)
    (F : ClusterFamily (I:={S // S∈P}) G w E)
    (hbranch : ∀ S,F.branch S={x | ∃ i∈S.val,x∈C.branch i})
    (H : SimpleGraph (SelectedResidualIndex P)) (hHtree : H.IsTree)
    (hH : H≤(C.selectedResidual hA P F hbranch).graph T)
    (Horiginal : SimpleGraph I) (hforest : Horiginal.IsAcyclic)
    (hprevious : ∀ i j : {i // i∉P.biUnion id},H.Adj (Sum.inr i) (Sum.inr j) ↔ Horiginal.Adj i.val j.val)
    (d credit originalCredit : I → ℝ) (oldRadius rootCredit : {S // S∈P} → ℝ)
    (L c b a edgeMax baseline : ℝ) (high : Finset {r // r∈selectedRoots P})
    (oldH : {S // S∈P} → SimpleGraph I) (holdH : ∀ S,oldH S≤C.graph T)
    (spare reserve future : {r // r∈selectedRoots P} → ℝ) (N q : ℕ)
    (hshort : PaidShortPhaseOutput (B:=B) C hA hT P F hbranch H d credit originalCredit
      oldRadius rootCredit L c high oldH holdH spare)
    (hbranchMax : ∀ S : Finset I,ConnectedWithin Horiginal S → Disjoint S (P.biUnion id) →
      (∃ x y,∃ p : Horiginal.Walk x y,p.IsPath ∧ (∀ i∈p.support,i∈S) ∧
        L≤pathMass (fun i => d i+1) p) → ∀ i∈S,((Horiginal.neighborFinset i)∩S).card≤2)
    (hmax : ∀ S : Finset I,Disjoint S (P.biUnion id) →
      ¬C.ShortCycleCore Horiginal d L B S ∧ ¬C.FourArmCore Horiginal d L B S)
    (hD : 0≤D) (hL : 0<L) (hc : 0≤c) (hb : 0≤b) (ha : 0≤a) (hMax : 0≤edgeMax)
    (hd : ∀ i,1≤d i ∧ d i≤D) (hrad : ∀ S,0≤oldRadius S ∧ oldRadius S≤E)
    (hC : ∀ i x,x∈C.branch i → ∀ y,y∈C.branch i →
      ∃ p : A.Walk x y,(∀ z∈p.support,z∈C.branch i) ∧ walkWeight w p≤d i)
    (hcredit : ∀ i,c*d i≤credit i) (hbase : ∀ i,c*b≤credit i)
    (hspare0 : ∀ r,0≤spare r) (hfuture0 : ∀ r,0≤future r)
    (hrootbase : ∀ r,c*baseline≤c*(mixedEffectiveDiameter d oldRadius r.val-1)+future r)
    (hbaseline : 0≤baseline) (hblockbase : baseline≤L-1)
    (hfuture : ∀ r,future r≤reserve r)
    (hbudget : ∀ r,r∈high → 2*c*edgeMax+2*(N:ℝ)*a+future r≤reserve r)
    (hrootbudget : ∀ r,5*(N:ℝ)*a+reserve r≤spare r)
    (hsize : 2*(2*L+(D+1))≤N*b) (hhalf : 2*a≤c*b)
    (hdonor : 2*(N:ℝ)*a≤c*L/4) (hcost : (N+1:ℕ)*a≤c*b/2)
    (hqa : (q:ℝ)*edgeMax≤a)
    (hdeg : ∀ i,i∉P.biUnion id → (C.graph B).degree i≤q)
    (hweight : ∀ e∈B.edgeSet,w e≤edgeMax) (hw0 : ∀ e∈B.edgeSet,0≤w e)
    (hloop : ∀ i x,x∈C.branch i → ∀ y,y∈C.branch i → ¬B.Adj x y)
    (hsingle : ∀ i j x,x∈C.branch i → ∀ y,y∈C.branch j →
      ∀ u,u∈C.branch i → ∀ v,v∈C.branch j → B.Adj x y → B.Adj u v → s(x,y)=s(u,v)) :
    ∃ Q : Finset (H.induce ((Finset.univ\selectedRoots P : Finset (SelectedResidualIndex P)):Set _)).ConnectedComponent,
    ∃ O : ResidualOwnership H (selectedRoots P),
      (∀ t,t∈Q ↔ ¬LongResidualComponent H (Finset.univ\selectedRoots P)
        (mixedEffectiveDiameter d oldRadius) L t) ∧
      let C0 := C.selectedResidual hA P F hbranch
      let prior := C.connectorPool hA hT oldH holdH Subtype.val ∪
        C0.connectorPool le_rfl hT (fun _ : {r // r∈selectedRoots P} => C0.graph T)
          (fun _ => le_rfl) (O.chosenFilled Q)
      FiniteRetainedPhaseOutput C G T B
        (max ((E+2*L)+4*(2*L+(D+1))+2*edgeMax) (2*L+(D+1)-1))
        c baseline (∑ i,originalCredit i) prior := by
  classical
  obtain ⟨Q,O,Fnew,radius,U,e,hQ,hnew,he,hrr,hwalk,hlong,hdis,hU,hfinal,Hnew,
    hHnew,hTree,hres,hpriorT,hpriorInternal,hpaid,hdeg2,hpaths,hmass⟩ :=
    reindex_paid_short_long_inputs C hA hT P F hbranch H hHtree hH Horiginal hprevious
      d credit originalCredit oldRadius rootCredit L c high hbranchMax oldH holdH spare hshort
  refine ⟨Q,O,hQ,?_⟩
  let C0 := C.selectedResidual hA P F hbranch
  let prior := C.connectorPool hA hT oldH holdH Subtype.val ∪
    C0.connectorPool le_rfl hT (fun _ : {r // r∈selectedRoots P} => C0.graph T)
      (fun _ => le_rfl) (O.chosenFilled Q)
  let rn := fun g => radius (e.symm g)
  let dn := fun i => mixedEffectiveDiameter d rn i-1
  let cn := selectedResidualCredit U (fun g => c*rn g+spare (e.symm g)) credit
  have hOldSub : P.biUnion id⊆U.biUnion id := by
    rw [hU]
    exact old_selected_subset_expanded P _ (chosenFilled_contains_roots O Q)
  have hUnonempty : U.Nonempty := by
    obtain ⟨S,hS⟩ := hP
    exact ⟨(e ⟨Sum.inl ⟨S,hS⟩,by simp [selectedRoots]⟩).val,
      (e ⟨Sum.inl ⟨S,hS⟩,by simp [selectedRoots]⟩).property⟩
  obtain ⟨hrn,hrootbase'⟩ := expanded_radius_bounds P U e d oldRadius radius E L c baseline future hc hrad hrootbase hrr
  obtain ⟨hroot0,hrootcap,hi,hcn0,hrootcredit,hrootbase''⟩ :=
    expanded_mixed_credit_inputs U d credit rn D (E+2*L) c b baseline
      (fun g => spare (e.symm g)) (fun g => future (e.symm g)) hc
      (fun g => hspare0 (e.symm g)) hd hcredit hbase hrn hrootbase'
  obtain ⟨hfuture',hbudget',hrootbudget'⟩ := reindexed_root_budgets P U e high spare reserve future c edgeMax a N
    hfuture hbudget hrootbudget
  have hconn : ConnectedWithin Hnew Finset.univ := by
    intro i _ j _
    obtain ⟨p⟩ := hTree.connected.preconnected i j
    exact ⟨p,by simp⟩
  have hdiam : ∀ i x,x∈(C.selectedResidual hA U (Fnew.reindex e.symm) hfinal).branch i →
      ∀ y,y∈(C.selectedResidual hA U (Fnew.reindex e.symm) hfinal).branch i →
      ∃ p : G.Walk x y,(∀ z∈p.support,z∈(C.selectedResidual hA U (Fnew.reindex e.symm) hfinal).branch i) ∧
        walkWeight w p≤dn i := by
    intro i x hx y hy
    have hw := C.selectedResidual_intrinsic hA U (Fnew.reindex e.symm) hfinal d rn hC
      (fun g => hwalk (e.symm g)) i x hx y hy
    cases i <;> simpa [dn,mixedEffectiveDiameter] using hw
  have hfuture0' (r : {r // r∈selectedRoots U}) : 0≤reindexedRootValue P U e future r := by
    obtain ⟨r,hr⟩ := r
    cases r with
    | inl g => exact hfuture0 (e.symm g)
    | inr i => simp [selectedRoots] at hr
  obtain ⟨Olong,Qlong,owner,rnext,keep,next,hnext,hcoverNext,hwalkNext,hint,hfresh,hkeep,hkeep0,hledger⟩ :=
    exists_constructed_retained_credit_family (hH:=hHnew) (hT:=hT) (d:=dn) (credit:=cn) (M:=D+1) (L:=L) (c:=c) (b:=b) (a:=a)
      (spare:=reindexedRootValue P U e spare) (reserve:=reindexedRootValue P U e reserve) (N:=N)
      C hA U (Fnew.reindex e.symm) hfinal hcover hunit hB hTree.isAcyclic hconn hUnonempty
      Horiginal hforest hres d rn (by funext i;dsimp [dn];ring)
      Finset.univ (P.biUnion id) (high.image e) (Finset.subset_univ _)
      (Finset.disjoint_left.mpr (fun i hi hp => (Finset.mem_sdiff.mp hi).2 (hOldSub hp)))
      (fun S _ hS => hmax S hS) edgeMax (reindexedRootValue P U e future)
      (by linarith) hL (by linarith) hMax hc ha hroot0
      (fun i _ => by linarith [(hd i).1]) (fun i _ => (hd i).2)
      (fun i hn => (hi i hn).1) (fun i hn => (hi i hn).2.1) hdeg2
      (by simpa only [dn,sub_add_cancel] using hmass) hdiam
      (fun i hn => (hi i hn).2.2.1) (fun i hn => (hi i hn).2.2.2) hcn0 hrootcredit
      hweight hfuture' hbudget' hsize hhalf hdonor hrootbudget' hcost q hqa
      (fun i hn => hdeg i (fun hp => hn (hOldSub hp))) hw0 hloop hsingle
      prior hpriorInternal (∑ i,originalCredit i) (E+2*L) baseline hrootcap hb hbaseline
      hblockbase hfuture0' hrootbase'' hpaid
  have hcoarse : ∀ i,∃ j,C.branch i⊆next.branch j := by
    apply C.coarsens_of_union next (fun j => originalMixedLabels U
      (retainedCarrier Olong Qlong _ owner j)) _ hcoverNext
    intro j
    rw [hnext j]
    exact C.mixed_union_branch_original hA U (Fnew.reindex e.symm) hfinal _
  apply finite_retained_phase_of_family C next rnext keep prior _ hcoverNext hcoarse hwalkNext hc hkeep hkeep0 hfresh _ hint hledger
  intro f hf
  rcases Finset.mem_union.mp hf with hf|hf
  · exact hpriorT f hf
  · exact (C.selectedResidual hA U (Fnew.reindex e.symm) hfinal).connectorPool_mem le_rfl hT _ _ _ hf

end MinorFreeSpanners
