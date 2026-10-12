import MinorFreeSpanners.ActiveRootHeavyAbsorption
import MinorFreeSpanners.UnpaidHeavyOwnerProvenance

/-! Prior paid root labels constrain the actual owners selected by unpaid
host edges. Only those genuinely eligible roots require a heavy-scale reserve;
all other roots retain their original metric and requested future ledger. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

 theorem actual_prior_paid_heavy_absorption {I V : Type*} [Fintype I] [Fintype V]
    {A T B G : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}
    (C : ClusterFamily (I:=I) A w D) (hA : A≤G) (hT : T≤G) (hB : B≤G)
    (hunit : ∀ e∈T.edgeSet,w e=1) (H : SimpleGraph I) (hH : H≤C.graph T)
    (P : Finset (Finset I)) (residual paid roots eligible : Finset I)
    (hprevious : roots\eligible⊆paid)
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
    (hfuture : ∀ j,future j≤spare j)
    (hbudget : ∀ j,j.val∈eligible → 2*c*M+2*(N:ℝ)*a+future j≤spare j) :
    ∃ owner : {S // S∈C.heavyAttachmentBlocks B P paid} → {r // r∈roots},
      (∀ S,(owner S).val∈eligible) ∧
      (∀ S,(owner S).val∉paid) ∧
      (∀ S,∃ x y,(∃ i∈root (owner S),x∈C.branch i) ∧
        (∃ i∈S.val,y∈C.branch i) ∧ s(x,y)∈C.unpaidTouchingEdges B S.val paid) ∧
      (∀ S∈P,S∉C.heavyAttachmentBlocks B P paid → C.unpaidTouchingEdges B S paid=∅) ∧
    let filled := fun j => root j∪assignedBlockUnion (C.heavyAttachmentBlocks B P paid) owner j
    (∀ j,(filled j).Nonempty) ∧
    (∀ i j,i≠j → Disjoint (filled i) (filled j)) ∧
    Finset.univ.biUnion filled=(Finset.univ.biUnion root)∪(C.heavyAttachmentBlocks B P paid).biUnion id ∧
    ∃ newRadius : {r // r∈roots} → ℝ,
      (∀ j,R j≤newRadius j ∧ newRadius j≤R j+2*M+2*(K-1)) ∧
      (∀ j,∀ x∈{x | ∃ i∈filled j,x∈C.branch i},∀ y∈{x | ∃ i∈filled j,x∈C.branch i},
        ∃ p : G.Walk x y,(∀ z∈p.support,∃ i∈filled j,z∈C.branch i) ∧ walkWeight w p≤newRadius j) ∧
      (∀ j,spent j+c*newRadius j+a*(assignedBlockUnion (C.heavyAttachmentBlocks B P paid) owner j).card+future j≤
        (∑ i∈filled j,credit i)+c*(∑ e∈C.connectorEdges hA hT (C.graph T) le_rfl (filled j),w e)) ∧
      (∑ j,(spent j+c*newRadius j+a*(assignedBlockUnion (C.heavyAttachmentBlocks B P paid) owner j).card+future j))≤
        (∑ i,credit i)+c*(∑ e∈T.edgeFinset,w e) := by
  classical
  obtain ⟨owner,source,target,hnotpaid,hs,ht,hedge,hw,hmem,hempty⟩ :=
    C.exists_unpaid_heavy_owner_provenance hB P residual paid roots root hroot_label M hweight hsub hcover hno
  have heligible : ∀ S,(owner S).val∈eligible := by
    intro S
    by_contra hn
    exact hnotpaid S (hprevious (Finset.mem_sdiff.mpr ⟨(owner S).property,hn⟩))
  refine ⟨owner,heligible,hnotpaid,fun S => ⟨source S,target S,hs S,ht S,hmem S⟩,hempty,?_⟩
  have hSP : C.heavyAttachmentBlocks B P paid⊆P := Finset.filter_subset _ _
  have hUP : (C.heavyAttachmentBlocks B P paid).biUnion id⊆P.biUnion id := by
    intro i hi
    obtain ⟨S,hS,hi⟩ := Finset.mem_biUnion.mp hi
    exact Finset.mem_biUnion.mpr ⟨S,hSP hS,hi⟩
  apply active_root_heavy_absorption C hA hT hunit H hH (C.heavyAttachmentBlocks B P paid)
    root owner rootGraph hrootGraph d credit source target R spare spent future L K M c a N
    hR hK hM hc ha hne hroots (fun j => (hrootP j).mono_right hUP)
    (fun S hS U hU => hdis S (hSP hS) U (hSP hU))
    (fun S hS => hgood S (hSP hS)) (fun S hS => hsize S (hSP hS))
    (fun i hi => hd i (hUP hi)) hdiam (fun i hi => hcredit i (hUP hi))
    (fun i hi => hbase i (hUP hi)) hcredit0 hs ht hedge hw hroot hrootcredit hfuture
  intro j hj
  obtain ⟨S,hS⟩ := hj
  obtain ⟨hS,ho⟩ := (mem_ownedBlocks (C.heavyAttachmentBlocks B P paid) owner j S).mp hS
  exact hbudget j (ho ▸ heligible ⟨S,hS⟩)

end MinorFreeSpanners
