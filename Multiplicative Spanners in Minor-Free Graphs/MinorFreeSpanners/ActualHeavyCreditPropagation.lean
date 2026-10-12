import MinorFreeSpanners.ActualSmallBlockHeavyAbsorption
import MinorFreeSpanners.ConnectorCreditExtension

/-! The actual small-block absorption is paid from the original root ledger.
Previously spent root credit is retained, and disjoint old root/block carriers
prevent repeated original vertex or unit-connector credit. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

 theorem actual_heavy_credit_propagation {I V : Type*} [Fintype I]
    {A T G : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}
    (C : ClusterFamily (I:=I) A w D) (hA : A≤G) (hT : T≤G)
    (hunit : ∀ e∈T.edgeSet,w e=1) (H J : SimpleGraph I)
    (hH : H≤C.graph T) (hJ : J≤C.graph T)
    (P : Finset (Finset I)) (root : Finset I) (d credit : I → ℝ)
    (source target : {S // S∈P} → V) (R L K M c a spare spent future : ℝ) (N : ℕ)
    (hR : 0≤R) (hK : 1≤K) (hM : 0≤M) (hc : 0≤c) (ha : 0≤a)
    (hdis : ∀ S∈P,∀ U∈P,S≠U → Disjoint S U)
    (hrootP : Disjoint root (P.biUnion id))
    (hgood : ∀ S∈P,∃ x y,∃ p : H.Walk x y,p.IsPath ∧ p.support.toFinset=S ∧
      L≤pathMass d p ∧ pathMass d p≤K)
    (hsize : ∀ S∈P,S.card≤N) (hd : ∀ i∈P.biUnion id,1≤d i)
    (hdiam : ∀ i x,x∈C.branch i → ∀ y,y∈C.branch i →
      ∃ q : A.Walk x y,(∀ z∈q.support,z∈C.branch i) ∧ walkWeight w q≤d i-1)
    (hcredit : ∀ i∈P.biUnion id,c*(d i-1)≤credit i)
    (hbase : ∀ i∈P.biUnion id,a≤credit i)
    (hs : ∀ S,∃ i∈root,source S∈C.branch i)
    (ht : ∀ S,∃ i∈S.val,target S∈C.branch i)
    (hedge : ∀ S,G.Adj (source S) (target S))
    (hweight : ∀ S,w s(source S,target S)≤M)
    (hroot : ∀ x∈{x | ∃ i∈root,x∈C.branch i},∀ y∈{x | ∃ i∈root,x∈C.branch i},
      ∃ p : G.Walk x y,(∀ z∈p.support,∃ i∈root,z∈C.branch i) ∧ walkWeight w p≤R)
    (hrootcredit : spent+c*R+spare≤(∑ i∈root,credit i)+
      c*(∑ e∈C.connectorEdges hA hT J hJ root,w e))
    (hbudget : 2*c*M+2*(N:ℝ)*a+future≤spare) :
    ∃ Q : Finset {S // S∈P},∃ newRadius : ℝ,Q.card≤2 ∧
      R≤newRadius ∧ newRadius≤R+2*M+2*(K-1) ∧
      (∀ x∈{x | ∃ i∈root∪P.biUnion id,x∈C.branch i},
        ∀ y∈{x | ∃ i∈root∪P.biUnion id,x∈C.branch i},∃ p : G.Walk x y,
          (∀ z∈p.support,∃ i∈root∪P.biUnion id,z∈C.branch i) ∧ walkWeight w p≤newRadius) ∧
      spent+c*newRadius+a*(P.biUnion id).card+future≤
        (∑ i∈root∪P.biUnion id,credit i)+
          c*(∑ e∈C.connectorEdges hA hT (C.graph T) le_rfl (root∪P.biUnion id),w e) := by
  classical
  obtain ⟨Q,r,hQ,hlo,hhi,hpaths,hpay⟩ := actual_small_block_heavy_absorption C hA hT hunit H hH
    P {x | ∃ i∈root,x∈C.branch i} d credit source target R L K M c a spare future N
    hR hK hM hc ha hdis hgood hsize hd hdiam hcredit hbase hs ht hedge hweight hroot hbudget
  have hmem (x : V) : (∃ i∈root∪P.biUnion id,x∈C.branch i) ↔
      ((∃ i∈root,x∈C.branch i) ∨ ∃ i∈P.biUnion id,x∈C.branch i) := by
    simp only [Finset.mem_union,or_and_right,exists_or]
  refine ⟨Q,r,hQ,hlo,hhi,?_,?_⟩
  · intro x hx y hy
    obtain ⟨p,hp,hw⟩ := hpaths x ((hmem x).mp hx) y ((hmem y).mp hy)
    exact ⟨p,fun z hz => (hmem z).mpr (hp z hz),hw⟩
  · have hh := C.root_block_credit_provenance hA hT H J hH hJ root P credit c R spare spent
      (c*r+a*(P.biUnion id).card+future) hc hrootP
      (fun e he => by rw [hunit e he];norm_num) hrootcredit hpay
    simpa only [add_assoc] using hh

end MinorFreeSpanners
