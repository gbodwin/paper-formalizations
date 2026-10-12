import MinorFreeSpanners.WeightedRootedAbsorption
import MinorFreeSpanners.PartialResidualOwnership

/-! Absorb only a chosen family of small residual components. Each root
keeps its actual radius and individual reserve budget; every unchosen
component stays outside all expanded root carriers. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

 theorem exists_partial_small_component_absorption {I V : Type*} [Fintype I]
    {A T G : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}
    (C : ClusterFamily (I:=I) A w D)
    (hA : A≤G) (hT : T≤G) (hunit : ∀ e∈T.edgeSet,w e=1)
    (H : SimpleGraph I) (hH : H≤C.graph T) (hconn : ConnectedWithin H Finset.univ)
    (roots : Finset I) (hne : roots.Nonempty)
    (Q : Finset (H.induce ((Finset.univ\roots : Finset I):Set I)).ConnectedComponent)
    (d credit : I → ℝ)
    (K Droot c b a : ℝ) (spare future : {r // r∈roots} → ℝ) (N : ℕ)
    (hroot : ∀ r∈roots,1≤d r) (hrootBound : ∀ r∈roots,d r-1≤Droot)
    (hK : 0≤K) (hc : 0≤c) (ha : 0≤a)
    (hdiam : ∀ i x,x∈C.branch i → ∀ y,y∈C.branch i →
      ∃ p : A.Walk x y,(∀ z∈p.support,z∈C.branch i) ∧ walkWeight w p≤d i-1)
    (hsmall : ∀ t : (H.induce ((Finset.univ\roots : Finset I):Set I)).ConnectedComponent,t∈Q →
      ∀ x y,∀ p : H.Walk x y,p.IsPath →
      (∀ i∈p.support,i∈ResidualComponents.block H (Finset.univ\roots) t) → pathMass d p≤K)
    (hcredit : ∀ i∉roots,c*(d i-1)≤credit i) (hbase : ∀ i∉roots,c*b≤credit i)
    (hsize : 2*K≤N*b) (hrelease : a≤c*b) (hbudget : ∀ r,N*a+future r≤spare r) :
    ∃ O : ResidualOwnership H roots,
    ∃ F : ClusterFamily (I:={r // r∈roots}) G w (Droot+2*K),
    ∃ radius : {r // r∈roots} → ℝ,
      (∀ r,F.branch r={x | ∃ i∈O.chosenFilled Q r,x∈C.branch i}) ∧
      (∀ x,(∃ r,x∈F.branch r) ↔
        ∃ i∈roots∪Q.biUnion (ResidualComponents.block H (Finset.univ\roots)),x∈C.branch i) ∧
      (∀ r,d r.val-1≤radius r ∧ radius r≤d r.val-1+2*K) ∧
      (∀ r x,x∈F.branch r → ∀ y,y∈F.branch r →
        ∃ p : G.Walk x y,(∀ z∈p.support,z∈F.branch r) ∧ walkWeight w p≤radius r) ∧
      (∀ r,c*radius r+a*(O.chosenAbsorbed Q r).card+future r≤c*(d r.val-1)+spare r+
        (∑ i∈O.chosenAbsorbed Q r,credit i)+
        c*(∑ e∈C.connectorEdges hA hT (C.graph T) le_rfl (O.chosenFilled Q r),w e)) ∧
      (∀ r s : {r // r∈roots},r≠s →
        Disjoint (C.connectorEdges hA hT (C.graph T) le_rfl (O.chosenFilled Q r))
          (C.connectorEdges hA hT (C.graph T) le_rfl (O.chosenFilled Q s))) := by
  classical
  obtain ⟨O⟩ := exists_residual_ownership H hconn roots hne
  have hone (r : {r // r∈roots}) : ∃ radius : ℝ,
      d r.val-1≤radius ∧ radius≤d r.val-1+2*K ∧
      (∀ x∈{x | ∃ i∈O.chosenFilled Q r,x∈C.branch i},∀ y∈{x | ∃ i∈O.chosenFilled Q r,x∈C.branch i},
        ∃ p : G.Walk x y,(∀ z∈p.support,∃ i∈O.chosenFilled Q r,z∈C.branch i) ∧ walkWeight w p≤radius) ∧
      c*radius+a*(O.chosenAbsorbed Q r).card+future r≤c*(d r.val-1)+spare r+
        (∑ i∈O.chosenAbsorbed Q r,credit i)+
        c*(∑ e∈C.connectorEdges hA hT (C.graph T) le_rfl (O.chosenFilled Q r),w e) := by
    have hport := fun t (_ : t∈O.chosenComponents Q r) => O.port_mem t
    have hbridge : ∀ t∈O.chosenComponents Q r,(C.graph T).Adj r.val (O.port t) := by
      intro t ht
      have he : O.owner t=r := (Finset.mem_filter.mp ht).2
      simpa only [he] using hH (O.adjacent t)
    obtain ⟨J,hJ,radius,hlo,hhi,hwalk,hpaid⟩ := weighted_rooted_absorption C hA hT hunit
      H hH (Finset.univ\roots) r.val (by simp [r.property])
      (O.chosenComponents Q r) O.port hport hbridge d credit K c b a (spare r) (future r) N
      (hroot r.val r.property) hK hc ha hdiam (fun t ht => hsmall t (Finset.mem_filter.mp ht).1)
      (fun i hi => hcredit i (Finset.mem_sdiff.mp hi).2)
      (fun i hi => hbase i (Finset.mem_sdiff.mp hi).2) hsize hrelease (hbudget r)
    refine ⟨radius,hlo,hhi,hwalk,?_⟩
    change c*radius+a*(O.chosenAbsorbed Q r).card+future r≤c*(d r.val-1)+spare r+
      (∑ i∈O.chosenAbsorbed Q r,credit i)+c*(∑ e∈C.connectorEdges hA hT J hJ (O.chosenFilled Q r),w e) at hpaid
    rw [C.connectorEdges_unit_weight hA hT J hJ (O.chosenFilled Q r) hunit] at hpaid
    rw [C.connectorEdges_unit_weight hA hT (C.graph T) le_rfl (O.chosenFilled Q r) hunit]
    have hs : internalEdges J (O.chosenFilled Q r)⊆internalEdges (C.graph T) (O.chosenFilled Q r) := by
      intro e he
      exact Finset.mem_filter.mpr ⟨edgeFinset_mono hJ (Finset.mem_filter.mp he).1,
        (Finset.mem_filter.mp he).2⟩
    have hcard : ((internalEdges J (O.chosenFilled Q r)).card:ℝ)≤(internalEdges (C.graph T) (O.chosenFilled Q r)).card :=
      by exact_mod_cast Finset.card_le_card hs
    nlinarith [mul_le_mul_of_nonneg_left hcard hc]
  choose radius hlo hhi hwalk hpaid using hone
  let F : ClusterFamily (I:={r // r∈roots}) G w (Droot+2*K) := {
    branch := fun r => {x | ∃ i∈O.chosenFilled Q r,x∈C.branch i}
    nonempty := by
      intro r
      obtain ⟨x,hx⟩ := C.nonempty r.val
      exact ⟨x,r.val,Finset.mem_insert_self _ _,hx⟩
    disjoint := by
      intro r s hrs
      apply Set.disjoint_left.mpr
      rintro x ⟨i,hi,hxi⟩ ⟨j,hj,hxj⟩
      by_cases he : i=j
      · exact Finset.disjoint_left.mp (O.chosenFilled_disjoint Q r s hrs) hi (he ▸ hj)
      · exact Set.disjoint_left.mp (C.disjoint i j he) hxi hxj
    connected := by
      intro r x hx y hy
      obtain ⟨p,hp,hw⟩ := hwalk r x hx y hy
      exact ⟨p,hp,hw.trans (by linarith [hhi r,hrootBound r.val r.property])⟩ }
  refine ⟨O,F,radius,fun _ => rfl,?_,fun r => ⟨hlo r,hhi r⟩,hwalk,hpaid,?_⟩
  · intro x
    constructor
    · rintro ⟨r,i,hi,hxi⟩
      refine ⟨i,?_,hxi⟩
      rw [←O.chosenFilled_union Q]
      exact Finset.mem_biUnion.mpr ⟨r,mem_univ _,hi⟩
    · rintro ⟨i,hi,hxi⟩
      rw [←O.chosenFilled_union Q] at hi
      obtain ⟨r,_,hir⟩ := Finset.mem_biUnion.mp hi
      exact ⟨r,i,hir,hxi⟩
  · intro r s hrs
    exact C.connectorEdges_disjoint hA hT (C.graph T) le_rfl _ _ (O.chosenFilled_disjoint Q r s hrs)

end MinorFreeSpanners
