import MinorFreeSpanners.ExactMixedTotalOutput
import MinorFreeSpanners.PriorCreditFromPhaseBills

/-! The same actual mixed heavy-phase witnesses now consume the preceding
high-degree marked-edge and weak-root touching-edge contracts directly. Their
retained mixed credit is constructed from actual kept root credit and unchanged
old residual credit. The independent aggregate prior-spending assumption is
removed; the common phase/geometry/scale instantiation remains explicit. -/
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
variable {d : SelectedResidualIndex P → ℝ} {M L c b a : ℝ}
variable {spare reserve : {r // r∈(selectedRoots P)} → ℝ} {N : ℕ}

variable (old : I → ℝ) (keep : {S // S∈P} → ℝ)


attribute [-instance] instDecidableEqSum in
 theorem total_output_from_phase_bills
    (high : Finset {S // S∈P})
    (hP : ∀ S U,S∈P → U∈P → S≠U → Disjoint S U)
    (Q : (r : {r // r∈(selectedRoots P)}) → RootedPathAssemblyResult (C.selectedResidual hA P F hbranch) le_rfl hT H hH
    (Finset.univ\(selectedRoots P)) r.val (O.components r) O.port (fun i => d i+1) (selectedResidualCredit P keep old) M L c b a (spare r) (reserve r) N)
    (hcover : ∀ x,∃ i,x∈C.branch i)
    (oldH : {S // S∈P} → SimpleGraph I) (holdH : ∀ S,oldH S≤C.graph T)
    (edgeMax : ℝ)
    (future : {r // r∈selectedRoots P} → ℝ)
    (hc : 0≤c) (hwT : ∀ e∈T.edgeSet,0≤w e) (hwE : ∀ e∈E.edgeSet,0≤w e)
    (hhigh : (∑ e∈C.markedEdges E (high.biUnion Subtype.val),w e)+(∑ S∈high,keep S)≤
      ∑ S∈high,∑ i∈S.val,old i)
    (hweak : ∀ S,S∉high → (∑ e∈C.touchingEdges E S.val,w e)+keep S≤
      (∑ i∈S.val,old i)+c*(∑ e∈C.connectorEdges hA hT (oldH S) (holdH S) S.val,w e))
    (hphase : ExactPriorPaidHeavyPhaseOutput O Q E (weakRootPrior P high) (highRootEligible P high) edgeMax future) :
    let active := (C.selectedResidual hA P F hbranch).heavyAttachmentBlocks E (smallBlocks O Q) (allPaidLabels O Q∪(weakRootPrior P high))
    ∃ owner : {S // S∈active} → {r // r∈selectedRoots P},
    ∃ rootRadius : {r // r∈selectedRoots P} → ℝ,
    ∃ blockRadius : {S // S∈leftovers O Q\active} → ℝ,
      (∀ S,(owner S).val∈(highRootEligible P high)) ∧
      (∀ S,(owner S).val∉allPaidLabels O Q∪(weakRootPrior P high)) ∧
      (∀ S,∃ x y,(∃ i∈rootCarrier O Q (owner S),x∈(C.selectedResidual hA P F hbranch).branch i) ∧
        (∃ i∈S.val,y∈(C.selectedResidual hA P F hbranch).branch i) ∧ s(x,y)∈(C.selectedResidual hA P F hbranch).unpaidTouchingEdges E S.val (allPaidLabels O Q∪(weakRootPrior P high))) ∧
      (∀ S∈leftovers O Q,S∉active → (C.selectedResidual hA P F hbranch).unpaidTouchingEdges E S (allPaidLabels O Q∪(weakRootPrior P high))=∅) ∧
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
      (∑ e∈E.edgeFinset,w e)+
        (∑ r,(c*rootRadius r+future r))+
        (∑ S : {S // S∈leftovers O Q\active},
          (c*blockRadius S+(if N<S.val.card then c*b/2 else 0)))≤
            (∑ i,old i)+c*(∑ e∈C.connectorPool hA hT oldH holdH Subtype.val ∪
              retainedConnectorPool O Q active owner,w e) := by
  have hprior := C.prior_credit_from_phase_bills hA hT P hP high oldH holdH old keep c hc hwT hwE hhigh hweak
  exact exact_mixed_total_output C hA P F hbranch O Q hcover oldH holdH
    (weakRootPrior P high) (highRootEligible P high) edgeMax (∑ i,old i) future hprior hphase

end AssembledPathFamilies
end MinorFreeSpanners
