import MinorFreeSpanners.RetainedInactiveBlocks
import MinorFreeSpanners.WeightedPathIntrinsicCredit
import MinorFreeSpanners.DisjointCreditPooling

/-! Inactive path blocks keep their actual intrinsic walks and credit. Their
budgets are pooled simultaneously with enlarged-root ledgers only after the
complete retained-carrier partition is proved disjoint. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

 theorem retained_path_block_pooling {I V J : Type*} [Fintype I] [Fintype V] [Fintype J]
    {A T G : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}
    (C : ClusterFamily (I:=I) A w D) (hA : A≤G) (hT : T≤G)
    (hunit : ∀ e∈T.edgeSet,w e=1) (H : SimpleGraph I) (hH : H≤C.graph T)
    (P active : Finset (Finset I)) (hactive : active⊆P)
    (root : J → Finset I) (owner : {S // S∈active} → J)
    (d credit : I → ℝ) (cost : J → ℝ) (L K c : ℝ) (hc : 0≤c)
    (hne : ∀ j,(root j).Nonempty)
    (hroots : ∀ i j,i≠j → Disjoint (root i) (root j))
    (hrootP : ∀ j,Disjoint (root j) (P.biUnion id))
    (hdis : ∀ S∈P,∀ U∈P,S≠U → Disjoint S U)
    (hgood : ∀ S∈P,∃ x y,∃ p : H.Walk x y,p.IsPath ∧ p.support.toFinset=S ∧
      L≤pathMass d p ∧ pathMass d p≤K)
    (hd : ∀ i∈P.biUnion id,1≤d i)
    (hdiam : ∀ i x,x∈C.branch i → ∀ y,y∈C.branch i →
      ∃ q : A.Walk x y,(∀ z∈q.support,z∈C.branch i) ∧ walkWeight w q≤d i-1)
    (hcredit : ∀ i∈P.biUnion id,c*(d i-1)≤credit i) (hcredit0 : ∀ i,0≤credit i)
    (hpaid : ∀ j,cost j≤(∑ i∈root j∪assignedBlockUnion active owner j,credit i)+
      c*(∑ e∈C.connectorEdges hA hT (C.graph T) le_rfl
        (root j∪assignedBlockUnion active owner j),w e)) :
    ∃ radius : {S // S∈P\active} → ℝ,
      (∀ S,0≤radius S ∧ L-1≤radius S ∧ radius S≤K-1 ∧
        ∀ x∈{x | ∃ i∈S.val,x∈C.branch i},∀ y∈{x | ∃ i∈S.val,x∈C.branch i},
          ∃ p : G.Walk x y,(∀ z∈p.support,∃ i∈S.val,z∈C.branch i) ∧ walkWeight w p≤radius S) ∧
      (∑ j,cost j)+(∑ S : {S // S∈P\active},c*radius S)≤
        (∑ i,credit i)+c*(∑ e∈T.edgeFinset,w e) := by
  classical
  have hneP (S) (hS : S∈P) : S.Nonempty := by
    obtain ⟨x,y,p,_,he,_,_⟩ := hgood S hS
    exact ⟨x,he ▸ List.mem_toFinset.mpr p.start_mem_support⟩
  have hpart := retained_inactive_partition P active hactive root owner hne hneP hroots hrootP hdis
  let Z := {S // S∈P\active}
  have hg (S : Z) := hgood S.val (Finset.mem_sdiff.mp S.property).1
  choose x y p hp he hlo hhi using hg
  let radius := fun S : Z => pathMass d (p S)-1
  have hin (S : Z) {i : I} (hi : i∈(p S).support) : i∈P.biUnion id :=
    Finset.mem_biUnion.mpr ⟨S.val,(Finset.mem_sdiff.mp S.property).1,he S ▸ List.mem_toFinset.mpr hi⟩
  have hpay (S : Z) := weighted_path_intrinsic_credit C hA hT hunit H hH (p S) (hp S)
    d credit L K c hc (fun i hi => hd i (hin S hi)) hdiam (hlo S) (hhi S)
    (fun i hi => hcredit i (hin S hi))
  refine ⟨radius,?_,?_⟩
  · intro S
    exact ⟨(hpay S).1,(hpay S).2.1,(hpay S).2.2.1,by simpa only [he S] using (hpay S).2.2.2.1⟩
  · let carrier : J⊕Z → Finset I :=
      Sum.elim (fun j => root j∪assignedBlockUnion active owner j) Subtype.val
    let coarse : J⊕Z → SimpleGraph I := Sum.elim (fun _ => C.graph T) (fun _ => H)
    have hcoarse (j : J⊕Z) : coarse j≤C.graph T := by cases j <;> first | exact le_rfl | exact hH
    let payment : J⊕Z → ℝ := Sum.elim cost (fun S => c*radius S)
    have hh := C.disjoint_credit_pooling hA hT coarse hcoarse carrier hpart.2.1
      credit payment c hc hcredit0 (fun e he => by rw [hunit e he];norm_num) (by
        intro j
        cases j with
        | inl j => exact hpaid j
        | inr S => simpa only [carrier,coarse,payment,Sum.elim_inr,he S] using (hpay S).2.2.2.2)
    simpa only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,payment] using hh

end MinorFreeSpanners
