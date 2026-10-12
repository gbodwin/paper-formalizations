import MinorFreeSpanners.AssembledPriorPaidPhase
import MinorFreeSpanners.AssembledPriorPaidWeight

/-! Prior-paid incidences are subtracted from the actual residual edge bill.
The same assembled output retains all carriers, intrinsic diameter credits
and futures, while heavy attachments use only eligible unpaid roots. Earlier
root expenditure and global scale instantiation remain separate obligations. -/
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


noncomputable def PriorPaidHeavyPhaseOutput (E : SimpleGraph V) (prior eligible : Finset I) (edgeMax : ℝ)
    (future : {r // r∈roots} → ℝ) : Prop :=
    let active := C.heavyAttachmentBlocks E (smallBlocks O Q) (allPaidLabels O Q∪prior)
    ∃ owner : {S // S∈active} → {r // r∈roots},
    ∃ rootRadius : {r // r∈roots} → ℝ,
    ∃ blockRadius : {S // S∈leftovers O Q\active} → ℝ,
      (∀ S,(owner S).val∈eligible) ∧
      (∀ S,(owner S).val∉allPaidLabels O Q∪prior) ∧
      (∀ S,∃ x y,(∃ i∈rootCarrier O Q (owner S),x∈C.branch i) ∧
        (∃ i∈S.val,y∈C.branch i) ∧ s(x,y)∈C.unpaidTouchingEdges E S.val (allPaidLabels O Q∪prior)) ∧
      (∀ S∈leftovers O Q,S∉active → C.unpaidTouchingEdges E S (allPaidLabels O Q∪prior)=∅) ∧
      let carrier : {r // r∈roots}⊕{S // S∈leftovers O Q\active} → Finset I :=
        Sum.elim (fun r => rootCarrier O Q r∪assignedBlockUnion active owner r) Subtype.val
      (∀ j,(carrier j).Nonempty) ∧
      (∀ i j,i≠j → Disjoint (carrier i) (carrier j)) ∧
      Finset.univ.biUnion carrier=Finset.univ ∧
      (∀ r,(Q r).radius≤rootRadius r ∧ rootRadius r≤(Q r).radius+2*edgeMax+2*(2*L+M-1)) ∧
      (∀ S,0≤blockRadius S ∧ L-1≤blockRadius S ∧ blockRadius S≤2*L+M-1) ∧
      (∀ j,∀ x∈{x | ∃ i∈carrier j,x∈C.branch i},∀ y∈{x | ∃ i∈carrier j,x∈C.branch i},
        ∃ p : G.Walk x y,(∀ z∈p.support,∃ i∈carrier j,z∈C.branch i) ∧
          walkWeight w p≤Sum.elim rootRadius blockRadius j) ∧
      (∑ e∈C.unpaidTouchingEdges E (Finset.univ\roots) prior,w e)+
        (∑ r,(c*rootRadius r+future r))+
        (∑ S : {S // S∈leftovers O Q\active},
          (c*blockRadius S+(if N<S.val.card then c*b/2 else 0)))≤
            (∑ i,credit i)+c*(∑ e∈T.edgeFinset,w e)

 theorem prior_paid_weighted_heavy_phase (hunit : ∀ e∈T.edgeSet,w e=1) (hE : E≤G)
    (hforest : H.IsAcyclic) (W U prior eligible : Finset I)
    (hprevious : roots\eligible⊆prior)
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
    (hfuture : ∀ r,future r≤reserve r)
    (hbudget : ∀ r,r.val∈eligible → 2*c*edgeMax+2*(N:ℝ)*a+future r≤reserve r)
    (q : ℕ) (hqa : (q:ℝ)*edgeMax≤a)
    (hdeg : ∀ i∉roots,(C.graph E).degree i≤q)
    (hw0 : ∀ e∈E.edgeSet,0≤w e)
    (hloop : ∀ i x,x∈C.branch i → ∀ y,y∈C.branch i → ¬E.Adj x y)
    (hsingle : ∀ i j x,x∈C.branch i → ∀ y,y∈C.branch j →
      ∀ u,u∈C.branch i → ∀ v,v∈C.branch j → E.Adj x y → E.Adj u v → s(x,y)=s(u,v)) :
    PriorPaidHeavyPhaseOutput O Q E prior eligible edgeMax future := by
  classical
  obtain ⟨owner,rootRadius,blockRadius,heligible,hnotpaid,hedges,hempty,hne,hdis,hcover,hrr,hbr,hwalk,hledger⟩ :=
    prior_paid_full_heavy_phase O Q hunit hE hforest W U prior eligible hprevious hRW hRU hmax edgeMax future
      hL hK hMax hc ha hroot0 hd0 hdD hd hdiam hcredit hbase hcredit0 hrootcredit hweight hfuture hbudget
  let active := C.heavyAttachmentBlocks E (smallBlocks O Q) (allPaidLabels O Q∪prior)
  have hactive : active⊆smallBlocks O Q := Finset.filter_subset _ _
  have hpaid := prior_unpaid_weight_payment O Q E hE prior active hactive owner hempty
    q edgeMax hMax ha hqa hdeg hw0 hweight hloop hsingle
  refine ⟨owner,rootRadius,blockRadius,heligible,hnotpaid,hedges,hempty,hne,hdis,hcover,hrr,hbr,hwalk,?_⟩
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
