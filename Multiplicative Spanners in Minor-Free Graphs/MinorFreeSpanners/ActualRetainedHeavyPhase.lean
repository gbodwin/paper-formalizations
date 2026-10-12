import MinorFreeSpanners.ActualUnpaidHeavyAbsorption
import MinorFreeSpanners.RetainedPathBlockPooling

/-! Original heavy-edge classification drives a full retained-carrier phase.
Active blocks attach through their chosen original edges; inactive blocks
keep their actual walks and intrinsic credit. All old labels and previously
spent root allocations occur in one disjoint global payment certificate. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

 theorem actual_retained_heavy_phase {I V : Type*} [Fintype I] [Fintype V]
    {A T B G : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}
    (C : ClusterFamily (I:=I) A w D) (hA : A≤G) (hT : T≤G) (hB : B≤G)
    (hunit : ∀ e∈T.edgeSet,w e=1) (H : SimpleGraph I) (hH : H≤C.graph T)
    (P : Finset (Finset I)) (residual paid roots : Finset I)
    (root : {r // r∈roots} → Finset I)
    (rootGraph : {r // r∈roots} → SimpleGraph I) (hrootGraph : ∀ j,rootGraph j≤C.graph T)
    (d credit : I → ℝ)
    (R spare spent future : {r // r∈roots} → ℝ) (L K M c a : ℝ) (N : ℕ)
    (hR : ∀ j,0≤R j) (hK : 1≤K) (hM : 0≤M) (hc : 0≤c) (ha : 0≤a)
    (hne : ∀ j,(root j).Nonempty)
    (hroots : ∀ i j,i≠j → Disjoint (root i) (root j))
    (hrootP : ∀ j,Disjoint (root j) (P.biUnion id))
    (hdis : ∀ S∈P,∀ U∈P,S≠U → Disjoint S U)
    (hgood : ∀ S∈P,∃ x y,∃ p : H.Walk x y,p.IsPath ∧ p.support.toFinset=S ∧
      L≤pathMass d p ∧ pathMass d p≤K)
    (hsize : ∀ S∈P,S.card≤N) (hd : ∀ i∈P.biUnion id,1≤d i)
    (hdiam : ∀ i x,x∈C.branch i → ∀ y,y∈C.branch i →
      ∃ q : A.Walk x y,(∀ z∈q.support,z∈C.branch i) ∧ walkWeight w q≤d i-1)
    (hcredit : ∀ i∈P.biUnion id,c*(d i-1)≤credit i)
    (hbase : ∀ i∈P.biUnion id,a≤credit i) (hcredit0 : ∀ i,0≤credit i)
    (hroot_label : ∀ r,r.val∈root r)
    (hweight : ∀ e∈B.edgeSet,w e≤M)
    (hsub : ∀ S∈P,S⊆residual)
    (hcover : ∀ i,i∈residual ∨ i∈paid ∨ i∈roots)
    (hno : ∀ i∈residual,∀ j∈residual,i∉paid → j∉paid →
      ∀ x∈C.branch i,∀ y∈C.branch j,¬B.Adj x y)
    (hroot : ∀ j,∀ x∈{x | ∃ i∈root j,x∈C.branch i},∀ y∈{x | ∃ i∈root j,x∈C.branch i},
      ∃ p : G.Walk x y,(∀ z∈p.support,∃ i∈root j,z∈C.branch i) ∧ walkWeight w p≤R j)
    (hrootcredit : ∀ j,spent j+c*R j+spare j≤(∑ i∈root j,credit i)+
      c*(∑ e∈C.connectorEdges hA hT (rootGraph j) (hrootGraph j) (root j),w e))
    (hbudget : ∀ j,2*c*M+2*(N:ℝ)*a+future j≤spare j) :
    let active := C.heavyAttachmentBlocks B P paid
    ∃ owner : {S // S∈active} → {r // r∈roots},
    ∃ rootRadius : {r // r∈roots} → ℝ,
    ∃ blockRadius : {S // S∈P\active} → ℝ,
      (∀ S,∃ x y,(∃ i∈root (owner S),x∈C.branch i) ∧
        (∃ i∈S.val,y∈C.branch i) ∧ s(x,y)∈C.unpaidTouchingEdges B S.val paid) ∧
      (∀ S∈P,S∉active → C.unpaidTouchingEdges B S paid=∅) ∧
      let carrier : {r // r∈roots}⊕{S // S∈P\active} → Finset I :=
        Sum.elim (fun j => root j∪assignedBlockUnion active owner j) Subtype.val
      (∀ j,(carrier j).Nonempty) ∧
      (∀ i j,i≠j → Disjoint (carrier i) (carrier j)) ∧
      Finset.univ.biUnion carrier=(Finset.univ.biUnion root)∪P.biUnion id ∧
      (∀ j,R j≤rootRadius j ∧ rootRadius j≤R j+2*M+2*(K-1)) ∧
      (∀ S,0≤blockRadius S ∧ L-1≤blockRadius S ∧ blockRadius S≤K-1) ∧
      (∀ j,∀ x∈{x | ∃ i∈carrier j,x∈C.branch i},∀ y∈{x | ∃ i∈carrier j,x∈C.branch i},
        ∃ p : G.Walk x y,(∀ z∈p.support,∃ i∈carrier j,z∈C.branch i) ∧
          walkWeight w p≤Sum.elim rootRadius blockRadius j) ∧
      (∑ j,(spent j+c*rootRadius j+a*(assignedBlockUnion active owner j).card+future j))+
        (∑ S : {S // S∈P\active},c*blockRadius S)≤
          (∑ i,credit i)+c*(∑ e∈T.edgeFinset,w e) := by
  classical
  obtain ⟨owner,hedges,hempty,_,_,_,r,hr,hwalk,hledger,_⟩ :=
    actual_unpaid_heavy_absorption C hA hT hB hunit H hH P residual paid roots root rootGraph
      hrootGraph d credit R spare spent future L K M c a N hR hK hM hc ha hne hroots hrootP
      hdis hgood hsize hd hdiam hcredit hbase hcredit0 hroot_label hweight hsub hcover hno
      hroot hrootcredit hbudget
  let active := C.heavyAttachmentBlocks B P paid
  have hactive : active⊆P := Finset.filter_subset _ _
  have hneP (S) (hS : S∈P) : S.Nonempty := by
    obtain ⟨x,y,p,_,he,_,_⟩ := hgood S hS
    exact ⟨x,he ▸ List.mem_toFinset.mpr p.start_mem_support⟩
  have hpart := retained_inactive_partition P active hactive root owner hne hneP hroots hrootP hdis
  obtain ⟨b,hb,hpool⟩ := retained_path_block_pooling C hA hT hunit H hH P active hactive root owner
    d credit (fun j => spent j+c*r j+a*(assignedBlockUnion active owner j).card+future j)
    L K c hc hne hroots hrootP hdis hgood hd hdiam hcredit hcredit0 hledger
  refine ⟨owner,r,b,hedges,hempty,hpart.1,hpart.2.1,hpart.2.2,hr,
    fun S => ⟨(hb S).1,(hb S).2.1,(hb S).2.2.1⟩,?_,hpool⟩
  intro j
  cases j with
  | inl j => exact hwalk j
  | inr S => exact (hb S).2.2.2

end MinorFreeSpanners
