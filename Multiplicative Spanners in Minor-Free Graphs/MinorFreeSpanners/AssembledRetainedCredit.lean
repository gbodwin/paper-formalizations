import MinorFreeSpanners.AssembledLargeBlockCredit
import MinorFreeSpanners.RetainedInactiveBlocks
import MinorFreeSpanners.WeightedPathIntrinsicCredit
import MinorFreeSpanners.DisjointCreditPooling

/-! All nonabsorbed blocks of the same actual path assembly are retained.
Large blocks keep their already proved allocation and future reserve; small
inactive blocks keep intrinsic credit. The final sum uses disjoint original
carriers, including the enlarged roots, exactly once. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable
namespace AssembledPathFamilies
variable {I V : Type*} [Fintype I] [Fintype V] {A T G : SimpleGraph V} {w : Sym2 V → ℝ} {D₀ : ℝ}
variable {C : ClusterFamily (I:=I) A w D₀} {hA : A≤G} {hT : T≤G}
variable {H : SimpleGraph I} {hH : H≤C.graph T} {roots : Finset I}
variable (O : ResidualOwnership H roots)
variable {d credit : I → ℝ} {M L c b a : ℝ} {spare future : {r // r∈roots} → ℝ} {N : ℕ}
variable (Q : (r : {r // r∈roots}) → RootedPathAssemblyResult C hA hT H hH
    (Finset.univ\roots) r.val (O.components r) O.port d credit M L c b a (spare r) (future r) N)

 theorem pooled_retained_credit (hunit : ∀ e∈T.edgeSet,w e=1)
    (active : Finset (Finset I)) (hactive : active⊆leftovers O Q)
    (owner : {S // S∈active} → {r // r∈roots}) (cost : {r // r∈roots} → ℝ)
    (hc : 0≤c) (hd : ∀ i∉roots,1≤d i)
    (hdiam : ∀ i x,x∈C.branch i → ∀ y,y∈C.branch i →
      ∃ q : A.Walk x y,(∀ z∈q.support,z∈C.branch i) ∧ walkWeight w q≤d i-1)
    (hcredit : ∀ i∉roots,c*(d i-1)≤credit i) (hcredit0 : ∀ i,0≤credit i)
    (hpaid : ∀ r,cost r≤(∑ i∈rootCarrier O Q r∪assignedBlockUnion active owner r,credit i)+
      c*(∑ e∈C.connectorEdges hA hT (C.graph T) le_rfl
        (rootCarrier O Q r∪assignedBlockUnion active owner r),w e)) :
    ∃ radius : {S // S∈leftovers O Q\active} → ℝ,
      (∀ S,0≤radius S ∧ L-1≤radius S ∧ radius S≤2*L+M-1 ∧
        ∀ x∈{x | ∃ i∈S.val,x∈C.branch i},∀ y∈{x | ∃ i∈S.val,x∈C.branch i},
          ∃ p : G.Walk x y,(∀ z∈p.support,∃ i∈S.val,z∈C.branch i) ∧ walkWeight w p≤radius S) ∧
      (∑ r,cost r)+(∑ S : {S // S∈leftovers O Q\active},
        (c*radius S+(if N<S.val.card then a*S.val.card+c*b/2 else 0)))≤
          (∑ i,credit i)+c*(∑ e∈T.edgeFinset,w e) := by
  classical
  let Z := {S // S∈leftovers O Q\active}
  have hlocal (S : Z) : ∃ radius : ℝ,0≤radius ∧ L-1≤radius ∧ radius≤2*L+M-1 ∧
      (∀ x∈{x | ∃ i∈S.val,x∈C.branch i},∀ y∈{x | ∃ i∈S.val,x∈C.branch i},
        ∃ p : G.Walk x y,(∀ z∈p.support,∃ i∈S.val,z∈C.branch i) ∧ walkWeight w p≤radius) ∧
      c*radius+(if N<S.val.card then a*S.val.card+c*b/2 else 0)≤
        (∑ i∈S.val,credit i)+c*(∑ e∈C.connectorEdges hA hT H hH S.val,w e) := by
    have hS := (Finset.mem_sdiff.mp S.property).1
    by_cases hlarge : N<S.val.card
    · obtain ⟨r,hlo,hL,hhi,hw,hpay⟩ := leftover_large_payment O Q hS hlarge
      exact ⟨r,hlo,hL,hhi,hw,by simpa only [hlarge,ite_true,add_assoc] using hpay⟩
    · obtain ⟨x,y,p,hp,he,hlo,hhi⟩ := leftover_good O Q hS
      have hin (i) (hi : i∈p.support) : i∉roots :=
        (Finset.mem_sdiff.mp (leftover_subset O Q hS (he ▸ List.mem_toFinset.mpr hi))).2
      have hh := weighted_path_intrinsic_credit C hA hT hunit H hH p hp d credit L (2*L+M) c hc
        (fun i hi => hd i (hin i hi)) hdiam hlo hhi.le (fun i hi => hcredit i (hin i hi))
      refine ⟨pathMass d p-1,hh.1,hh.2.1,hh.2.2.1,?_,?_⟩
      · simpa only [he] using hh.2.2.2.1
      · simpa only [he,hlarge,ite_false,add_zero] using hh.2.2.2.2
  choose radius hrad using hlocal
  have hp := full_partition O Q
  have hpart := retained_inactive_partition (leftovers O Q) active hactive (rootCarrier O Q) owner
    hp.1 hp.2.2.1 hp.2.1 hp.2.2.2.2.1 hp.2.2.2.1
  refine ⟨radius,fun S => ⟨(hrad S).1,(hrad S).2.1,(hrad S).2.2.1,(hrad S).2.2.2.1⟩,?_⟩
  let carrier : {r // r∈roots}⊕Z → Finset I :=
    Sum.elim (fun r => rootCarrier O Q r∪assignedBlockUnion active owner r) Subtype.val
  let coarse : {r // r∈roots}⊕Z → SimpleGraph I := Sum.elim (fun _ => C.graph T) (fun _ => H)
  have hcoarse (j : {r // r∈roots}⊕Z) : coarse j≤C.graph T := by
    cases j <;> first | exact le_rfl | exact hH
  let payment : {r // r∈roots}⊕Z → ℝ := Sum.elim cost
    (fun S => c*radius S+(if N<S.val.card then a*S.val.card+c*b/2 else 0))
  have hh := C.disjoint_credit_pooling hA hT coarse hcoarse carrier hpart.2.1 credit payment c hc
    hcredit0 (fun e he => by rw [hunit e he];norm_num) (by
      intro j
      cases j with
      | inl r => exact hpaid r
      | inr S => exact (hrad S).2.2.2.2)
  simpa only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,payment] using hh

end AssembledPathFamilies
end MinorFreeSpanners
