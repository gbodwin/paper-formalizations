import MinorFreeSpanners.AssembledSmallHeavyOutput
import MinorFreeSpanners.AssembledRetainedCredit

/-! A full heavy phase on the same constructed root-fiber path assembly.
Every previous old label is retained; actual unpaid edges choose active-block
owners, while all inactive large and small blocks keep their proved credit.
Previously spent allocations and future reserves share one original ledger.
The remaining charge-to-total-heavy-edge-weight bound is a separate obligation. -/
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

 theorem full_heavy_phase (hunit : ∀ e∈T.edgeSet,w e=1) (hE : E≤G)
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
    ∃ owner : {S // S∈active} → {r // r∈roots},
    ∃ rootRadius : {r // r∈roots} → ℝ,
    ∃ blockRadius : {S // S∈leftovers O Q\active} → ℝ,
      (∀ S,∃ x y,(∃ i∈rootCarrier O Q (owner S),x∈C.branch i) ∧
        (∃ i∈S.val,y∈C.branch i) ∧ s(x,y)∈C.unpaidTouchingEdges E S.val (allPaidLabels O Q)) ∧
      (∀ S∈leftovers O Q,S∉active → C.unpaidTouchingEdges E S (allPaidLabels O Q)=∅) ∧
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
      (∑ r,(rootSpent O Q r+c*rootRadius r+a*(assignedBlockUnion active owner r).card+future r))+
        (∑ S : {S // S∈leftovers O Q\active},
          (c*blockRadius S+(if N<S.val.card then a*S.val.card+c*b/2 else 0)))≤
            (∑ i,credit i)+c*(∑ e∈T.edgeFinset,w e) := by
  classical
  obtain ⟨owner,radius,hedges,hempty,hr,hwalk,hpaid⟩ := small_heavy_output O Q hunit hE
    hforest W U hRW hRU hmax edgeMax future hL hK hMax hc ha hroot0 hd0 hdD hd hdiam
    hcredit hbase hcredit0 hrootcredit hweight hbudget
  let active := C.heavyAttachmentBlocks E (smallBlocks O Q) (allPaidLabels O Q)
  have hactiveSmall : active⊆smallBlocks O Q := Finset.filter_subset _ _
  have hactive : active⊆leftovers O Q := hactiveSmall.trans (smallBlocks_subset O Q)
  obtain ⟨blockRadius,hblock,hpool⟩ := pooled_retained_credit O Q hunit active hactive owner
    (fun r => rootSpent O Q r+c*radius r+a*(assignedBlockUnion active owner r).card+future r)
    hc (fun i hi => by have hh := hd i hi;linarith)
    (by simpa only [add_sub_cancel_right] using hdiam)
    (by simpa only [add_sub_cancel_right] using hcredit) hcredit0 hpaid
  have hp := full_partition O Q
  have hpart := retained_inactive_partition (leftovers O Q) active hactive (rootCarrier O Q) owner
    hp.1 hp.2.2.1 hp.2.1 hp.2.2.2.2.1 hp.2.2.2.1
  refine ⟨owner,radius,blockRadius,hedges,?_,hpart.1,hpart.2.1,
    hpart.2.2.trans hp.2.2.2.2.2,hr,
    fun S => ⟨(hblock S).1,(hblock S).2.1,(hblock S).2.2.1⟩,?_,hpool⟩
  · intro S hS hnot
    by_cases hlarge : N<S.card
    · exact large_unpaid_empty O Q hS hlarge
    · exact hempty S (Finset.mem_filter.mpr ⟨hS,by omega⟩) hnot
  · intro j
    cases j with
    | inl r => exact hwalk r
    | inr S => exact (hblock S).2.2.2

end AssembledPathFamilies
end MinorFreeSpanners
