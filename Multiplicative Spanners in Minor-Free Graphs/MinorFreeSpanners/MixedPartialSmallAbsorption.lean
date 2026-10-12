import MinorFreeSpanners.PartialSmallAbsorption
import MinorFreeSpanners.MixedSmallAbsorptionPhase
import MinorFreeSpanners.MixedOriginalEdgeTransport
import MinorFreeSpanners.SelectedRootCreditTransfer

/-! Partial absorption uses actual original residual degrees, even after large
roots have been collapsed. Root credit and individual reserve provenance are
retained, and unchosen components are not absorbed. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

attribute [-instance] instDecidableEqSum in
 theorem exists_mixed_partial_small_absorption {I V : Type*} [Fintype I] [Fintype V]
    {A B T G : SimpleGraph V} {w : Sym2 V → ℝ} {D E : ℝ}
    (C : ClusterFamily (I:=I) A w D) (hcover : ∀ x,∃ i,x∈C.branch i)
    (hA : A≤G) (hB : B≤G) (hT : T≤G)
    (hunit : ∀ e∈T.edgeSet,w e=1)
    (P : Finset (Finset I)) (hP : P.Nonempty)
    (F : ClusterFamily (I:={S // S∈P}) G w E)
    (hbranch : ∀ S,F.branch S={x | ∃ i∈S.val,x∈C.branch i})
    (d credit : I → ℝ) (oldRadius rootCredit : {S // S∈P} → ℝ)
    (hrad : ∀ S,0≤oldRadius S ∧ oldRadius S≤E)
    (hC : ∀ i x,x∈C.branch i → ∀ y,y∈C.branch i →
      ∃ p : A.Walk x y,(∀ z∈p.support,z∈C.branch i) ∧ walkWeight w p≤d i)
    (hF : ∀ S x,x∈F.branch S → ∀ y,y∈F.branch S →
      ∃ p : G.Walk x y,(∀ z∈p.support,z∈F.branch S) ∧ walkWeight w p≤oldRadius S)
    (H : SimpleGraph (SelectedResidualIndex P))
    (hH : H≤(C.selectedResidual hA P F hbranch).graph T)
    (hconn : ConnectedWithin H Finset.univ)
    (Q : Finset (H.induce ((Finset.univ\selectedRoots P : Finset (SelectedResidualIndex P)):Set _)).ConnectedComponent)
    (K c b M : ℝ) (spare future : {r // r∈selectedRoots P} → ℝ) (N q : ℕ) (hK : 0≤K) (hc : 0≤c) (hM : 0≤M)
    (hsmall :
      ∀ t : (H.induce ((Finset.univ\selectedRoots P : Finset (SelectedResidualIndex P)):Set _)).ConnectedComponent,
        t∈Q → ∀ x y,∀ p : H.Walk x y,p.IsPath →
          (∀ i∈p.support,i∈ResidualComponents.block H (Finset.univ\selectedRoots P) t) →
            pathMass (mixedEffectiveDiameter d oldRadius) p≤K)
    (hcredit : ∀ i,i∉P.biUnion id → c*d i≤credit i)
    (hbase : ∀ i,i∉P.biUnion id → c*b≤credit i)
    (hdeg : ∀ i,i∉P.biUnion id → (C.graph B).degree i≤q)
    (hweight : ∀ e∈B.edgeSet,w e≤M)
    (hloop : ∀ i x,x∈C.branch i → ∀ y,y∈C.branch i → ¬B.Adj x y)
    (hsingle : ∀ i j x,x∈C.branch i → ∀ y,y∈C.branch j →
      ∀ u,u∈C.branch i → ∀ v,v∈C.branch j →
      B.Adj x y → B.Adj u v → s(x,y)=s(u,v))
    (hsize : 2*K≤N*b) (hrelease : (q:ℝ)*M≤c*b)
    (hbudget : ∀ r,N*((q:ℝ)*M)+future r≤spare r) :
    let C0 := C.selectedResidual hA P F hbranch
    let roots := selectedRoots P
    ∃ O : ResidualOwnership H roots,
    ∃ Fnew : ClusterFamily (I:={r // r∈roots}) G w (E+2*K),
    ∃ radius : {r // r∈roots} → ℝ,
      (∀ r,Fnew.branch r={x | ∃ i∈O.chosenFilled Q r,x∈C0.branch i}) ∧
      (∀ x,(∃ r,x∈Fnew.branch r) ↔
        ∃ i∈roots∪Q.biUnion (ResidualComponents.block H (Finset.univ\roots)),x∈C0.branch i) ∧
      (∀ r,mixedEffectiveDiameter d oldRadius r.val-1≤radius r ∧
        radius r≤mixedEffectiveDiameter d oldRadius r.val-1+2*K) ∧
      (∀ r x,x∈Fnew.branch r → ∀ y,y∈Fnew.branch r →
        ∃ p : G.Walk x y,(∀ z∈p.support,z∈Fnew.branch r) ∧ walkWeight w p≤radius r) ∧
      (∀ r,c*radius r+((q:ℝ)*M)*(O.chosenAbsorbed Q r).card+future r≤
        c*(mixedEffectiveDiameter d oldRadius r.val-1)+spare r+
        (∑ i∈O.chosenAbsorbed Q r,selectedResidualCredit P rootCredit credit i)+
        c*(∑ e∈C0.connectorEdges le_rfl hT (C0.graph T) le_rfl (O.chosenFilled Q r),w e)) ∧
      (∀ r,(∑ e∈C0.touchingEdges B (O.chosenAbsorbed Q r),w e)≤((q:ℝ)*M)*(O.chosenAbsorbed Q r).card) ∧
      (∀ r s : {r // r∈roots},r≠s →
        Disjoint (C0.connectorEdges le_rfl hT (C0.graph T) le_rfl (O.chosenFilled Q r))
          (C0.connectorEdges le_rfl hT (C0.graph T) le_rfl (O.chosenFilled Q s))) ∧
      (∀ r e,e∈C0.connectorEdges le_rfl hT (C0.graph T) le_rfl (O.chosenFilled Q r) →
        ∀ j x y,x∈C0.branch j → y∈C0.branch j → e≠s(x,y)) := by
  let C0 := C.selectedResidual hA P F hbranch
  let roots := selectedRoots P
  have hne : roots.Nonempty := by
    obtain ⟨S,hS⟩ := hP
    exact ⟨Sum.inl ⟨S,hS⟩,by simp [roots,selectedRoots]⟩
  have hr : ∀ r∈roots,1≤mixedEffectiveDiameter d oldRadius r := by
    intro r hr
    cases r with
    | inl S => simp only [mixedEffectiveDiameter,Sum.elim_inl];linarith [(hrad S).1]
    | inr i => simp [roots,selectedRoots] at hr
  have hrB : ∀ r∈roots,mixedEffectiveDiameter d oldRadius r-1≤E := by
    intro r hr
    cases r with
    | inl S => simpa [mixedEffectiveDiameter] using (hrad S).2
    | inr i => simp [roots,selectedRoots] at hr
  have hd := C.selectedResidual_intrinsic hA P F hbranch d oldRadius hC hF
  have hd' : ∀ i x,x∈C0.branch i → ∀ y,y∈C0.branch i →
      ∃ p : G.Walk x y,(∀ z∈p.support,z∈C0.branch i) ∧
        walkWeight w p≤mixedEffectiveDiameter d oldRadius i-1 := by
    intro i x hx y hy
    obtain ⟨p,hp,hw⟩ := hd i x hx y hy
    refine ⟨p,hp,?_⟩
    cases i <;> simpa [mixedEffectiveDiameter] using hw
  have hcred : ∀ i∉roots,c*(mixedEffectiveDiameter d oldRadius i-1)≤selectedResidualCredit P rootCredit credit i := by
    intro i hi
    cases i with
    | inl S => exact (hi (by simp [roots,selectedRoots])).elim
    | inr i => simpa [mixedEffectiveDiameter,selectedResidualCredit] using hcredit i.val i.property
  have hbas : ∀ i∉roots,c*b≤selectedResidualCredit P rootCredit credit i := by
    intro i hi
    cases i with
    | inl S => exact (hi (by simp [roots,selectedRoots])).elim
    | inr i => exact hbase i.val i.property
  obtain ⟨O,Fnew,radius,hbranch',hcover',hrad',hwalk,hpaid,hdis⟩ :=
    exists_partial_small_component_absorption C0 le_rfl hT hunit H hH hconn roots hne Q
      (mixedEffectiveDiameter d oldRadius) (selectedResidualCredit P rootCredit credit) K E c b ((q:ℝ)*M) spare future N
      hr hrB hK hc (mul_nonneg (Nat.cast_nonneg q) hM) hd' hsmall hcred hbas hsize hrelease hbudget
  have hres (r : {r // r∈roots}) (t : {S // S∈P}) : Sum.inl t∉O.chosenAbsorbed Q r := by
    intro ht
    exact (Finset.mem_sdiff.mp (O.absorbed_residual r (O.chosenAbsorbed_subset Q r ht))).2 (by simp [roots,selectedRoots])
  have hedge (r : {r // r∈roots}) := C.mixed_touching_weight_le hA hB P F hbranch hcover
    (O.chosenAbsorbed Q r) (hres r) q M hM hdeg hweight hloop hsingle
  exact ⟨O,Fnew,radius,hbranch',hcover',hrad',hwalk,hpaid,hedge,hdis,
    fun r e he j x y hx hy => C0.connectorEdges_fresh le_rfl hT (C0.graph T) le_rfl
      (O.chosenFilled Q r) he j x y hx hy⟩

end MinorFreeSpanners
