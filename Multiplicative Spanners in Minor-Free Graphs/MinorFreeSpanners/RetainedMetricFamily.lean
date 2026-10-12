import MinorFreeSpanners.ExpandedBillsTotalOutput
import MinorFreeSpanners.IntrinsicCarrierFamily

/-! The same paid retained carriers form a covering metric family, and its
entire literal connector history is internal to those new branches. The next
level can therefore use freshness without replacing any connector identity. -/
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
variable {spare reserve : {r // r∈selectedRoots P} → ℝ} {N : ℕ}

attribute [-instance] instDecidableEqSum in
 theorem retained_metric_family_from_expanded_bills
    (Q : (r : {r // r∈selectedRoots P}) → RootedPathAssemblyResult (C.selectedResidual hA P F hbranch)
      le_rfl hT H hH (Finset.univ\selectedRoots P) r.val (O.components r) O.port
      (fun i => d i+1) credit M L c b a (spare r) (reserve r) N)
    (hcover : ∀ x,∃ i,x∈C.branch i)
    (priorEdges : Finset (Sym2 V))
    (hinternal : ∀ e∈priorEdges,∃ g x y,x∈F.branch g ∧ y∈F.branch g ∧ e=s(x,y))
    (high : Finset {S // S∈P}) (edgeMax initial rootBound baseline : ℝ)
    (future : {r // r∈selectedRoots P} → ℝ) (hroot : ∀ r : {r // r∈selectedRoots P},d r.val≤rootBound)
    (hc : 0≤c) (hb : 0≤b) (hbaseline : 0≤baseline) (hblockbase : baseline≤L-1)
    (hfuture0 : ∀ r,0≤future r)
    (hrootbase : ∀ r : {r // r∈selectedRoots P},c*baseline≤c*d r.val+future r)
    (hprior : (∑ e∈C.touchingEdges E ((Finset.univ\high).biUnion Subtype.val),w e)+
      (∑ e∈C.markedEdges E (high.biUnion Subtype.val),w e)+
      (∑ i,credit i)≤ initial+c*(∑ e∈priorEdges,w e))
    (hphase : ExactPriorPaidHeavyPhaseOutput O Q E (weakRootPrior P high)
      (highRootEligible P high) edgeMax future) :
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
  classical
  intro active
  obtain ⟨owner,rootRadius,blockRadius,_,_,_,_,hne,hdis,hall,hrr,hbr,hwalk,hfresh,hpaid⟩ :=
    total_output_from_expanded_bills C hA P F hbranch O Q hcover priorEdges hinternal
      high edgeMax initial future hprior hphase
  let C0 := C.selectedResidual hA P F hbranch
  let carrier := retainedCarrier O Q active owner
  let radius := Sum.elim rootRadius blockRadius
  have hcap : ∀ j,radius j≤max (rootBound+4*(2*L+M)+2*edgeMax) (2*L+M-1) := by
    intro j
    cases j with
    | inl r =>
      apply le_trans _ (le_max_left _ _)
      have hh := (Q r).radius_upper
      have hnew := (hrr r).2
      have hold := hroot r
      dsimp [radius]
      simp only [add_sub_cancel_right] at hh
      linarith
    | inr S => exact (hbr S).2.2.trans (le_max_right _ _)
  let next := C0.ofIntrinsicCarriers carrier hne hdis radius hcap hwalk
  have hbranches : ∀ j,next.branch j={x | ∃ i∈carrier j,x∈C0.branch i} := fun _ => rfl
  have hlabels : ∀ i,∃ j,i∈carrier j := by
    intro i
    have hi : i∈Finset.univ.biUnion carrier := hall ▸ mem_univ i
    obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hi
    exact ⟨j,hj⟩
  let newH := Sum.elim (fun _ : {r // r∈selectedRoots P} => C0.graph T)
    (fun _ : {S // S∈leftovers O Q\active} => H)
  have hnewH : ∀ j,newH j≤C0.graph T := by
    intro j
    cases j <;> first | exact le_rfl | exact hH
  have hist : ∀ e∈priorEdges,∃ i x y,x∈C0.branch i ∧ y∈C0.branch i ∧ e=s(x,y) := by
    intro e he
    obtain ⟨g,x,y,hx,hy,heq⟩ := hinternal e he
    exact ⟨Sum.inl g,x,y,hx,hy,heq⟩
  let keep := Sum.elim (fun r => c*rootRadius r+future r)
    (fun S : {S // S∈leftovers O Q\active} => c*blockRadius S+(if N<S.val.card then c*b/2 else 0))
  have hkeep : ∀ j,c*max (radius j) baseline≤keep j := by
    intro j
    cases j with
    | inl r =>
      change c*max (rootRadius r) baseline≤c*rootRadius r+future r
      by_cases hr : rootRadius r≤baseline
      · rw [max_eq_right hr]
        have hlo := (Q r).radius_lower
        simp only [add_sub_cancel_right] at hlo
        have hh := (hrr r).1
        have hbase := hrootbase r
        nlinarith
      · rw [max_eq_left (le_of_not_ge hr)]
        linarith [hfuture0 r]
    | inr S =>
      change c*max (blockRadius S) baseline≤c*blockRadius S+(if N<S.val.card then c*b/2 else 0)
      rw [max_eq_left (hblockbase.trans (hbr S).2.1)]
      have hn : 0≤c*b/2 := div_nonneg (mul_nonneg hc hb) (by norm_num)
      split_ifs <;> linarith
  have hkeep0 : ∀ j,0≤keep j := fun j =>
    (mul_nonneg hc (hbaseline.trans (le_max_right _ _))).trans (hkeep j)
  refine ⟨owner,radius,keep,next,hbranches,
    C0.union_family_covers next carrier hbranches (C.selectedResidual_covers hA P F hbranch hcover) hlabels,
    hwalk,?_,hfresh,hkeep,hkeep0,?_⟩
  · exact C0.merged_internal_connector_union le_rfl hT next carrier hbranches hlabels newH hnewH priorEdges hist
  · simpa only [keep,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,add_assoc] using hpaid

end AssembledPathFamilies
end MinorFreeSpanners
