import MinorFreeSpanners.WeightedSelectedDonorAbsorption
import MinorFreeSpanners.WeightedLargePathBlock
import MinorFreeSpanners.ResidualBlockRemainder

/-! A finite residual path-family assembly is constructed from the actual
forest and attachment ports. One root absorbs the selected blocks and pays
all short endpoint allocations; every other large block pays itself. The
full disjoint carrier partition is retained, including all still-small
interior blocks. Their heavy-edge assignment is a later step. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

 theorem weighted_residual_path_assembly {I V : Type*} [Fintype I]
    {B T G : SimpleGraph V} {w : Sym2 V → ℝ} {D₀ : ℝ}
    (C : ClusterFamily (I:=I) B w D₀) (hB : B≤G) (hT : T≤G)
    (hunit : ∀ e∈T.edgeSet,w e=1) (H : SimpleGraph I) (hH : H≤C.graph T)
    (hforest : H.IsAcyclic) (R : Finset I) (root : I) (hr : root∉R)
    (F : Finset (H.induce (R:Set I)).ConnectedComponent)
    (port : (H.induce (R:Set I)).ConnectedComponent → I)
    (hport : ∀ t∈F,port t∈ResidualComponents.block H R t)
    (hbridge : ∀ t∈F,(C.graph T).Adj root (port t))
    (d credit : I → ℝ) (M L c b a spare future : ℝ) (N : ℕ)
    (hM : 0≤M) (hL : 0<L) (hroot : 1≤d root) (hc : 0≤c) (ha : 0≤a)
    (hdeg : ∀ i∈R,((H.neighborFinset i)∩R).card≤2)
    (hd : ∀ i∈R,2≤d i) (hdM : ∀ i∈R,d i≤M)
    (hm : ∀ t∈F,L≤∑ i∈ResidualComponents.block H R t,d i)
    (hdiam : ∀ i x,x∈C.branch i → ∀ y,y∈C.branch i →
      ∃ p : B.Walk x y,(∀ z∈p.support,z∈C.branch i) ∧ walkWeight w p≤d i-1)
    (hcredit : ∀ i∈R,c*(d i-1)≤credit i) (hbase : ∀ i∈R,c*b≤credit i)
    (hsize : 2*(2*L+M)≤N*b) (hhalf : 2*a≤c*b)
    (hdonor : 2*(N:ℝ)*a≤c*L/4) (hbudget : 5*(N:ℝ)*a+future≤spare)
    (hcost : (N+1:ℕ)*a≤c*b/2) :
    ∃ P : (H.induce (R:Set I)).ConnectedComponent → Finset (Finset I),
    ∃ selected ends : (H.induce (R:Set I)).ConnectedComponent → Finset I,
      (∀ t∈F,ResidualAttachmentPartition H R t d M L N (port t) (P t) (selected t) (ends t)) ∧
      let U := F.biUnion selected
      let rootBlock := insert root U
      let rest := (F.biUnion P)\(F.image selected)
      let out := insert rootBlock rest
      (∀ S∈out,S.Nonempty) ∧
      (∀ S∈out,∀ T∈out,S≠T → Disjoint S T) ∧
      out.biUnion id=insert root (F.biUnion (ResidualComponents.block H R)) ∧
      (∃ J : SimpleGraph I,∃ hJ : J≤C.graph T,∃ radius : ℝ,
        d root-1≤radius ∧ radius≤d root-1+2*(2*L+M) ∧
        (∀ x∈{x | ∃ i∈rootBlock,x∈C.branch i},∀ y∈{x | ∃ i∈rootBlock,x∈C.branch i},
          ∃ p : G.Walk x y,(∀ z∈p.support,∃ i∈rootBlock,z∈C.branch i) ∧ walkWeight w p≤radius) ∧
        c*radius+a*U.card+(∑ t∈F,a*(ends t).card)+future≤
          c*(d root-1)+spare+(∑ i∈U,credit i)+
            c*(∑ e∈C.connectorEdges hB hT J hJ rootBlock,w e)) ∧
      (∀ S∈rest,N<S.card → ∃ radius : ℝ,0≤radius ∧ L-1≤radius ∧ radius≤2*L+M-1 ∧
        (∀ x∈{x | ∃ i∈S,x∈C.branch i},∀ y∈{x | ∃ i∈S,x∈C.branch i},
          ∃ p : G.Walk x y,(∀ z∈p.support,∃ i∈S,z∈C.branch i) ∧ walkWeight w p≤radius) ∧
        c*radius+a*S.card+c*b/2≤(∑ i∈S,credit i)+
          c*(∑ e∈C.connectorEdges hB hT H hH S,w e)) := by
  classical
  obtain ⟨P,A,ends,hpart,_,hpaid⟩ := weighted_selected_donor_absorption C hB hT hunit H hH
    hforest R root hr F port hport hbridge d credit M L c b a spare future N
    hM hL hroot hc ha hdeg hd hdM hm hdiam hcredit hbase hsize hhalf hdonor hbudget
  obtain ⟨hne,hdis,hcover,hrest⟩ := residual_attachment_remainder H R F d M L N port P A ends hpart root hr
  refine ⟨P,A,ends,hpart,hne,hdis,hcover,hpaid,?_⟩
  intro S hS hlarge
  obtain ⟨t,ht,hSt,_⟩ := hrest S hS
  obtain ⟨x,y,p,hp,he,hlo,hhi⟩ := (hpart t ht).good S hSt
  have hSR : S⊆R := by
    intro i hi
    apply ResidualComponents.subset H R t
    rw [←(hpart t ht).cover]
    exact Finset.mem_biUnion.mpr ⟨S,hSt,hi⟩
  have hpR : ∀ i∈p.support,i∈R := fun i hi => hSR (he ▸ List.mem_toFinset.mpr hi)
  have hlen : N<p.length+1 := by
    have hcard : S.card=p.length+1 := by
      rw [←he,List.toFinset_card_of_nodup hp.support_nodup,Walk.length_support]
    omega
  have h := weighted_large_path_block C hB hT hunit H hH p hp d credit
    L (2*L+M) c b a N hc ha (fun i hi => by have hh:=hd i (hpR i hi);linarith)
    hdiam hlo hhi.le (fun i hi => hbase i (hpR i hi)) hlen (by linarith) hcost
  simpa only [he,Set.mem_ofPred_eq] using h

end MinorFreeSpanners
