import MinorFreeSpanners.WeightedHeavyBlockAbsorption
import MinorFreeSpanners.WeightedPathIntrinsicCredit

/-! Actual disjoint small path blocks and their original unit connectors
supply both intrinsic and releasing credit. Selected heavy host edges attach
them to an existing root carrier; the proof constructs its radius and a
reserve of at most two actual blocks without treating heavy edges as MST credit. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

 theorem actual_small_block_heavy_absorption {I V : Type*} [Fintype I]
    {A T G : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}
    (C : ClusterFamily (I:=I) A w D) (hA : A≤G) (hT : T≤G)
    (hunit : ∀ e∈T.edgeSet,w e=1) (H : SimpleGraph I) (hH : H≤C.graph T)
    (P : Finset (Finset I)) (root : Set V) (d credit : I → ℝ)
    (source target : {S // S∈P} → V) (R L K M c a spare future : ℝ) (N : ℕ)
    (hR : 0≤R) (hK : 1≤K) (hM : 0≤M) (hc : 0≤c) (ha : 0≤a)
    (hdis : ∀ S∈P,∀ U∈P,S≠U → Disjoint S U)
    (hgood : ∀ S∈P,∃ x y,∃ p : H.Walk x y,p.IsPath ∧ p.support.toFinset=S ∧
      L≤pathMass d p ∧ pathMass d p≤K)
    (hsize : ∀ S∈P,S.card≤N) (hd : ∀ i∈P.biUnion id,1≤d i)
    (hdiam : ∀ i x,x∈C.branch i → ∀ y,y∈C.branch i →
      ∃ q : A.Walk x y,(∀ z∈q.support,z∈C.branch i) ∧ walkWeight w q≤d i-1)
    (hcredit : ∀ i∈P.biUnion id,c*(d i-1)≤credit i)
    (hbase : ∀ i∈P.biUnion id,a≤credit i)
    (hs : ∀ S,source S∈root)
    (ht : ∀ S,∃ i∈S.val,target S∈C.branch i)
    (hedge : ∀ S,G.Adj (source S) (target S))
    (hweight : ∀ S,w s(source S,target S)≤M)
    (hroot : ∀ x∈root,∀ y∈root,∃ p : G.Walk x y,
      (∀ z∈p.support,z∈root) ∧ walkWeight w p≤R)
    (hbudget : 2*c*M+2*(N:ℝ)*a+future≤spare) :
    ∃ Q : Finset {S // S∈P},∃ newRadius : ℝ,Q.card≤2 ∧
      R≤newRadius ∧ newRadius≤R+2*M+2*(K-1) ∧
      (∀ x∈{x | x∈root ∨ ∃ i∈P.biUnion id,x∈C.branch i},
        ∀ y∈{x | x∈root ∨ ∃ i∈P.biUnion id,x∈C.branch i},∃ p : G.Walk x y,
          (∀ z∈p.support,z∈root ∨ ∃ i∈P.biUnion id,z∈C.branch i) ∧ walkWeight w p≤newRadius) ∧
      c*newRadius+a*(P.biUnion id).card+future≤c*R+spare+
        (∑ i∈P.biUnion id,credit i)+c*(∑ e∈P.biUnion (fun S => C.connectorEdges hA hT H hH S),w e) := by
  classical
  let J := {S // S∈P}
  have hg (S : J) := hgood S.val S.property
  choose x y p hp he hlo hhi using hg
  let radius := fun S : J => pathMass d (p S)-1
  let block := fun S : J => {x | ∃ i∈S.val,x∈C.branch i}
  let funds := fun S : J => (∑ i∈S.val,credit i)+c*(∑ e∈C.connectorEdges hA hT H hH S.val,w e)
  have hin (S : J) {i : I} (hi : i∈S.val) : i∈P.biUnion id :=
    Finset.mem_biUnion.mpr ⟨S.val,S.property,hi⟩
  have hpay (S : J) := weighted_path_intrinsic_credit C hA hT hunit H hH (p S) (hp S)
    d credit L K c hc (fun i hi => hd i (hin S (he S ▸ List.mem_toFinset.mpr hi))) hdiam
    (hlo S) (hhi S) (fun i hi => hcredit i (hin S (he S ▸ List.mem_toFinset.mpr hi)))
  have hr (S : J) : radius S≤K-1 := (hpay S).2.2.1
  have hpaid (S : J) : c*radius S≤funds S := by
    simpa only [he S] using (hpay S).2.2.2.2
  have hwalk (S : J) : ∀ u∈block S,∀ v∈block S,∃ q : G.Walk u v,
      (∀ z∈q.support,z∈block S) ∧ walkWeight w q≤radius S := by
    dsimp only [block,radius]
    simpa only [he S,Set.mem_ofPred_eq] using (hpay S).2.2.2.1
  have hrel (S : J) : a*S.val.card≤funds S := by
    have hb : a*S.val.card≤∑ i∈S.val,credit i := by
      calc
        _ = ∑ _i∈S.val,a := by simp [mul_comm]
        _ ≤ _ := Finset.sum_le_sum fun i hi => hbase i (hin S hi)
    have he0 : 0≤c*(∑ e∈C.connectorEdges hA hT H hH S.val,w e) := by
      rw [C.connectorEdges_unit_weight hA hT H hH S.val hunit]
      exact mul_nonneg hc (Nat.cast_nonneg _)
    exact le_add_of_le_of_nonneg hb he0
  obtain ⟨Q,newRadius,_,hQ,hloR,hhiR,hpaths,hcost⟩ :=
    weighted_heavy_block_absorption w (Finset.univ : Finset J) root block source target
      radius funds (fun S => S.val.card) R (K-1) M c a spare future N
      hR (by linarith) hM ha (fun S _ => hs S) (fun S _ => ht S)
      (fun S _ => hedge S) (fun S _ => hweight S) hroot (fun S _ => hwalk S)
      (fun S _ => hr S) (fun S _ => hsize S.val S.property)
      (fun S _ => hpaid S) (fun S _ => hrel S) hbudget
  have hcarrier : {z | z∈root ∨ ∃ S∈(Finset.univ : Finset J),z∈block S}=
      {z | z∈root ∨ ∃ i∈P.biUnion id,z∈C.branch i} := by
    ext z
    simp only [Set.mem_ofPred_eq,Finset.mem_univ,true_and,block]
    constructor
    · rintro (hz | ⟨S,i,hi,hz⟩)
      · exact Or.inl hz
      · exact Or.inr ⟨i,hin S hi,hz⟩
    · rintro (hz | ⟨i,hi,hz⟩)
      · exact Or.inl hz
      · obtain ⟨S,hS,hi⟩ := Finset.mem_biUnion.mp hi
        exact Or.inr ⟨⟨S,hS⟩,i,hi,hz⟩
  have hdP : (↑P : Set (Finset I)).PairwiseDisjoint id := hdis
  have hsizes : (∑ S : J,(S.val.card:ℝ))=((P.biUnion id).card:ℝ) := by
    rw [←Finset.sum_subtype P (fun _ => Iff.rfl) (fun S => (S.card:ℝ))]
    exact_mod_cast (Finset.card_biUnion hdP).symm
  have hcredits : (∑ S : J,∑ i∈S.val,credit i)=∑ i∈P.biUnion id,credit i := by
    rw [←Finset.sum_subtype P (fun _ => Iff.rfl) (fun S => ∑ i∈S,credit i)]
    exact (Finset.sum_biUnion hdP).symm
  have hedges : (∑ S : J,∑ e∈C.connectorEdges hA hT H hH S.val,w e)=
      ∑ e∈P.biUnion (fun S => C.connectorEdges hA hT H hH S),w e := by
    rw [←Finset.sum_subtype P (fun _ => Iff.rfl) (fun S => ∑ e∈C.connectorEdges hA hT H hH S,w e)]
    symm
    apply Finset.sum_biUnion
    intro S hS U hU hSU
    exact C.connectorEdges_disjoint hA hT H hH S U (hdis S hS U hU hSU)
  refine ⟨Q,newRadius,hQ,hloR,hhiR,?_,?_⟩
  · intro u hu v hv
    obtain ⟨p,hp,hw⟩ := hpaths u ((Set.ext_iff.mp hcarrier u).mpr hu)
      v ((Set.ext_iff.mp hcarrier v).mpr hv)
    exact ⟨p,fun z hz => (Set.ext_iff.mp hcarrier z).mp (hp z hz),hw⟩
  · dsimp [funds] at hcost
    rw [Finset.sum_add_distrib,←Finset.mul_sum,hsizes,hcredits,hedges] at hcost
    simpa only [add_assoc] using hcost

end MinorFreeSpanners
