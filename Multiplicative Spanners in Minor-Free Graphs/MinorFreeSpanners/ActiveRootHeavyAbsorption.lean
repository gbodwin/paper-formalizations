import MinorFreeSpanners.SimultaneousHeavyAbsorption

/-! Only a root with a genuinely nonempty assigned block family needs the
heavy-scale absorption reserve. Every other root keeps its original carrier,
walk radius and prior ledger, requiring only its requested future reserve. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

 theorem active_root_heavy_absorption {I V J : Type*} [Fintype I] [Fintype V] [Fintype J]
    {A T G : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}
    (C : ClusterFamily (I:=I) A w D) (hA : A≤G) (hT : T≤G)
    (hunit : ∀ e∈T.edgeSet,w e=1) (H : SimpleGraph I) (hH : H≤C.graph T)
    (P : Finset (Finset I)) (root : J → Finset I) (owner : {S // S∈P} → J)
    (rootGraph : J → SimpleGraph I) (hrootGraph : ∀ j,rootGraph j≤C.graph T)
    (d credit : I → ℝ) (source target : {S // S∈P} → V)
    (R spare spent future : J → ℝ) (L K M c a : ℝ) (N : ℕ)
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
    (hs : ∀ S,∃ i∈root (owner S),source S∈C.branch i)
    (ht : ∀ S,∃ i∈S.val,target S∈C.branch i)
    (hedge : ∀ S,G.Adj (source S) (target S))
    (hweight : ∀ S,w s(source S,target S)≤M)
    (hroot : ∀ j,∀ x∈{x | ∃ i∈root j,x∈C.branch i},∀ y∈{x | ∃ i∈root j,x∈C.branch i},
      ∃ p : G.Walk x y,(∀ z∈p.support,∃ i∈root j,z∈C.branch i) ∧ walkWeight w p≤R j)
    (hrootcredit : ∀ j,spent j+c*R j+spare j≤(∑ i∈root j,credit i)+
      c*(∑ e∈C.connectorEdges hA hT (rootGraph j) (hrootGraph j) (root j),w e))
    (hfuture : ∀ j,future j≤spare j)
    (hbudget : ∀ j,(ownedBlocks P owner j).Nonempty → 2*c*M+2*(N:ℝ)*a+future j≤spare j) :
    let filled := fun j => root j∪assignedBlockUnion P owner j
    (∀ j,(filled j).Nonempty) ∧
    (∀ i j,i≠j → Disjoint (filled i) (filled j)) ∧
    Finset.univ.biUnion filled=(Finset.univ.biUnion root)∪P.biUnion id ∧
    ∃ newRadius : J → ℝ,
      (∀ j,R j≤newRadius j ∧ newRadius j≤R j+2*M+2*(K-1)) ∧
      (∀ j,∀ x∈{x | ∃ i∈filled j,x∈C.branch i},∀ y∈{x | ∃ i∈filled j,x∈C.branch i},
        ∃ p : G.Walk x y,(∀ z∈p.support,∃ i∈filled j,z∈C.branch i) ∧ walkWeight w p≤newRadius j) ∧
      (∀ j,spent j+c*newRadius j+a*(assignedBlockUnion P owner j).card+future j≤
        (∑ i∈filled j,credit i)+c*(∑ e∈C.connectorEdges hA hT (C.graph T) le_rfl (filled j),w e)) ∧
      (∑ j,(spent j+c*newRadius j+a*(assignedBlockUnion P owner j).card+future j))≤
        (∑ i,credit i)+c*(∑ e∈T.edgeFinset,w e) := by
  classical
  let filled := fun j => root j∪assignedBlockUnion P owner j
  have hpart := owned_block_partition P root owner hne hroots hrootP hdis
  refine ⟨hpart.1,hpart.2.1,hpart.2.2,?_⟩
  have hlocal (j : J) : ∃ r : ℝ,R j≤r ∧ r≤R j+2*M+2*(K-1) ∧
      (∀ x∈{x | ∃ i∈filled j,x∈C.branch i},∀ y∈{x | ∃ i∈filled j,x∈C.branch i},
        ∃ p : G.Walk x y,(∀ z∈p.support,∃ i∈filled j,z∈C.branch i) ∧ walkWeight w p≤r) ∧
      spent j+c*r+a*(assignedBlockUnion P owner j).card+future j≤
        (∑ i∈filled j,credit i)+c*(∑ e∈C.connectorEdges hA hT (C.graph T) le_rfl (filled j),w e) := by
    let Pj := ownedBlocks P owner j
    rcases Finset.eq_empty_or_nonempty Pj with hempty | hnePj
    · have haempty : assignedBlockUnion P owner j=∅ := by
        rw [←ownedBlocks_union]
        change Pj.biUnion id=∅
        rw [hempty]
        simp
      have hfilled : filled j=root j := by simp only [filled,haempty,Finset.union_empty]
      refine ⟨R j,le_rfl,by linarith,?_,?_⟩
      · simpa only [hfilled] using hroot j
      · rw [hfilled,haempty,Finset.card_empty,Nat.cast_zero,mul_zero,add_zero]
        have hsub := C.connectorEdges_mono_graph_carrier hA hT
          (rootGraph j) (C.graph T) (hrootGraph j) le_rfl (hrootGraph j)
          (S:=root j) (U:=root j) subset_rfl
        have hsum := Finset.sum_le_sum_of_subset_of_nonneg (f:=w) hsub (fun e he _ => by
          rw [hunit e (C.connectorEdges_mem hA hT (C.graph T) le_rfl (root j) he)]
          norm_num)
        have hh := mul_le_mul_of_nonneg_left hsum hc
        linarith [hrootcredit j,hfuture j]
    ·
      let emb : {S // S∈Pj} → {S // S∈P} :=
        fun S => ⟨S.val,ownedBlocks_subset P owner j S.property⟩
      have ho (S : {S // S∈Pj}) : owner (emb S)=j :=
        ((mem_ownedBlocks P owner j S.val).mp S.property).choose_spec
      have hsub := ownedBlocks_union_subset P owner j
      obtain ⟨Q,r,_,hlo,hhi,hpaths,hpay⟩ := actual_heavy_credit_propagation C hA hT hunit H
        (rootGraph j) hH (hrootGraph j) Pj (root j) d credit (source ∘ emb) (target ∘ emb)
        (R j) L K M c a (spare j) (spent j) (future j) N (hR j) hK hM hc ha
        (fun S hS U hU => hdis S (ownedBlocks_subset P owner j hS) U (ownedBlocks_subset P owner j hU))
        ((hrootP j).mono_right hsub)
        (fun S hS => hgood S (ownedBlocks_subset P owner j hS))
        (fun S hS => hsize S (ownedBlocks_subset P owner j hS))
        (fun i hi => hd i (hsub hi)) hdiam (fun i hi => hcredit i (hsub hi))
        (fun i hi => hbase i (hsub hi))
        (fun S => by simpa only [ho S,Function.comp_apply] using hs (emb S))
        (fun S => ht (emb S)) (fun S => hedge (emb S)) (fun S => hweight (emb S))
        (hroot j) (hrootcredit j) (hbudget j hnePj)
      refine ⟨r,hlo,hhi,?_,?_⟩
      · simpa only [Pj,ownedBlocks_union,filled] using hpaths
      · simpa only [Pj,ownedBlocks_union,filled] using hpay
  choose newRadius hnew using hlocal
  refine ⟨newRadius,fun j => ⟨(hnew j).1,(hnew j).2.1⟩,
    fun j => (hnew j).2.2.1,fun j => (hnew j).2.2.2,?_⟩
  exact C.disjoint_credit_pooling hA hT (fun _ => C.graph T) (fun _ => le_rfl) filled
    hpart.2.1 credit _ c hc hcredit0 (fun e he => by rw [hunit e he];norm_num)
    (fun j => (hnew j).2.2.2)

end MinorFreeSpanners
