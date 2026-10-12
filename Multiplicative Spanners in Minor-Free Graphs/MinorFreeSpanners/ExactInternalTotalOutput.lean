import MinorFreeSpanners.ExactMixedPriorPayment
import MinorFreeSpanners.InternalPriorOriginalPayment

/-! Preserve every actual mixed heavy-phase witness while pooling the literal
retained prior connector union. Only its proved internality is used to show
freshness, so no canonical representative is silently replaced. -/
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
 theorem exact_internal_total_output
    (Q : (r : {r // r∈(selectedRoots P)}) → RootedPathAssemblyResult (C.selectedResidual hA P F hbranch) le_rfl hT H hH
    (Finset.univ\(selectedRoots P)) r.val (O.components r) O.port (fun i => d i+1) credit M L c b a (spare r) (reserve r) N)
    (hcover : ∀ x,∃ i,x∈C.branch i)
    (priorEdges : Finset (Sym2 V))
    (hinternal : ∀ e∈priorEdges,∃ g x y,x∈F.branch g ∧ y∈F.branch g ∧ e=s(x,y))
    (prior eligible : Finset (SelectedResidualIndex P)) (edgeMax initial : ℝ)
    (future : {r // r∈selectedRoots P} → ℝ)
    (hprior : (∑ e∈C.touchingEdges E (originalMixedLabels P prior),w e)+
      (∑ e∈C.markedEdges E (P.biUnion id\originalMixedLabels P prior),w e)+
      (∑ i,credit i)≤ initial+c*(∑ e∈priorEdges,w e))
    (hphase : ExactPriorPaidHeavyPhaseOutput O Q E prior eligible edgeMax future) :
    let active := (C.selectedResidual hA P F hbranch).heavyAttachmentBlocks E (smallBlocks O Q) (allPaidLabels O Q∪prior)
    ∃ owner : {S // S∈active} → {r // r∈selectedRoots P},
    ∃ rootRadius : {r // r∈selectedRoots P} → ℝ,
    ∃ blockRadius : {S // S∈leftovers O Q\active} → ℝ,
      (∀ S,(owner S).val∈eligible) ∧
      (∀ S,(owner S).val∉allPaidLabels O Q∪prior) ∧
      (∀ S,∃ x y,(∃ i∈rootCarrier O Q (owner S),x∈(C.selectedResidual hA P F hbranch).branch i) ∧
        (∃ i∈S.val,y∈(C.selectedResidual hA P F hbranch).branch i) ∧ s(x,y)∈(C.selectedResidual hA P F hbranch).unpaidTouchingEdges E S.val (allPaidLabels O Q∪prior)) ∧
      (∀ S∈leftovers O Q,S∉active → (C.selectedResidual hA P F hbranch).unpaidTouchingEdges E S (allPaidLabels O Q∪prior)=∅) ∧
      let carrier : {r // r∈selectedRoots P}⊕{S // S∈leftovers O Q\active} → Finset (SelectedResidualIndex P) :=
        Sum.elim (fun r => rootCarrier O Q r∪assignedBlockUnion active owner r) Subtype.val
      (∀ j,(carrier j).Nonempty) ∧
      (∀ i j,i≠j → Disjoint (carrier i) (carrier j)) ∧
      Finset.univ.biUnion carrier=Finset.univ ∧
      (∀ r,(Q r).radius≤rootRadius r ∧ rootRadius r≤(Q r).radius+2*edgeMax+2*(2*L+M-1)) ∧
      (∀ S,0≤blockRadius S ∧ L-1≤blockRadius S ∧ blockRadius S≤2*L+M-1) ∧
      (∀ j,∀ x∈{x | ∃ i∈carrier j,x∈(C.selectedResidual hA P F hbranch).branch i},∀ y∈{x | ∃ i∈carrier j,x∈(C.selectedResidual hA P F hbranch).branch i},
        ∃ p : G.Walk x y,(∀ z∈p.support,∃ i∈carrier j,z∈(C.selectedResidual hA P F hbranch).branch i) ∧
          walkWeight w p≤Sum.elim rootRadius blockRadius j) ∧
      Disjoint priorEdges (retainedConnectorPool O Q active owner) ∧
      (∑ e∈E.edgeFinset,w e)+
        (∑ r,(c*rootRadius r+future r))+
        (∑ S : {S // S∈leftovers O Q\active},
          (c*blockRadius S+(if N<S.val.card then c*b/2 else 0)))≤
            initial+c*(∑ e∈priorEdges ∪
              retainedConnectorPool O Q active owner,w e) := by
  classical
  obtain ⟨owner,rootRadius,blockRadius,heligible,hnotpaid,hedges,hempty,hne,hdis,hcover',hrr,hbr,hwalk,hledger⟩ := hphase
  let active := (C.selectedResidual hA P F hbranch).heavyAttachmentBlocks E
    (smallBlocks O Q) (allPaidLabels O Q∪prior)
  refine ⟨owner,rootRadius,blockRadius,heligible,hnotpaid,hedges,hempty,hne,hdis,hcover',hrr,hbr,hwalk,?_⟩
  let newH : {r // r∈selectedRoots P}⊕{S // S∈leftovers O Q\active} → SimpleGraph (SelectedResidualIndex P) :=
    Sum.elim (fun _ => (C.selectedResidual hA P F hbranch).graph T) (fun _ => H)
  have hnewH (j : {r // r∈selectedRoots P}⊕{S // S∈leftovers O Q\active}) :
      newH j≤(C.selectedResidual hA P F hbranch).graph T := by
    cases j <;> first | exact le_rfl | exact hH
  have hh := C.internal_prior_original_payment hA hT P F hbranch hcover priorEdges hinternal newH hnewH
    (retainedCarrier O Q active owner) prior credit initial
    ((∑ r,(c*rootRadius r+future r))+
      ∑ S : {S // S∈leftovers O Q\active},(c*blockRadius S+(if N<S.val.card then c*b/2 else 0))) c
    hprior (by
      change _ ≤ _ + c*(∑ e∈retainedConnectorPool O Q active owner,w e)
      simpa only [add_assoc] using hledger)
  refine ⟨hh.1,?_⟩
  have hpaid := hh.2
  change _ ≤ initial+c*(∑ e∈priorEdges ∪ retainedConnectorPool O Q active owner,w e) at hpaid
  simpa only [add_assoc] using hpaid

end AssembledPathFamilies
end MinorFreeSpanners
