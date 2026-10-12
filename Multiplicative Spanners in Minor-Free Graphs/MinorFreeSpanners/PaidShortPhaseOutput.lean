import MinorFreeSpanners.PaidShortComponentAbsorption

/-! The full short-absorption result, keeping its original edge bills,
retained complement credit and exact two-stage connector union. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

attribute [-instance] instDecidableEqSum in
@[irreducible] noncomputable def PaidShortPhaseOutput {I V : Type*} [Fintype I] [Fintype V]
    {A B T G : SimpleGraph V} {w : Sym2 V → ℝ} {D E : ℝ}
    (C : ClusterFamily (I:=I) A w D) (hA : A≤G) (hT : T≤G)
    (P : Finset (Finset I)) (F : ClusterFamily (I:={S // S∈P}) G w E)
    (hbranch : ∀ S,F.branch S={x | ∃ i∈S.val,x∈C.branch i})
    (H : SimpleGraph (SelectedResidualIndex P))
    (d credit originalCredit : I → ℝ) (oldRadius rootCredit : {S // S∈P} → ℝ)
    (K c : ℝ) (high : Finset {r // r∈selectedRoots P})
    (oldH : {S // S∈P} → SimpleGraph I) (holdH : ∀ S,oldH S≤C.graph T)
    (future : {r // r∈selectedRoots P} → ℝ) : Prop :=
    let C0 := C.selectedResidual hA P F hbranch
    let roots := selectedRoots P
    ∃ Q : Finset (H.induce ((Finset.univ\roots : Finset (SelectedResidualIndex P)):Set _)).ConnectedComponent,
    ∃ O : ResidualOwnership H roots,
    ∃ Fnew : ClusterFamily (I:={r // r∈roots}) G w (E+2*K),
    ∃ radius : {r // r∈roots} → ℝ,
      (∀ t,t∈Q ↔ ¬LongResidualComponent H (Finset.univ\roots) (mixedEffectiveDiameter d oldRadius) K t) ∧
      (∀ r,Fnew.branch r={x | ∃ i∈O.chosenFilled Q r,x∈C0.branch i}) ∧
      (∀ x,(∃ r,x∈Fnew.branch r) ↔
        ∃ i∈roots∪Q.biUnion (ResidualComponents.block H (Finset.univ\roots)),x∈C0.branch i) ∧
      (∀ r,mixedEffectiveDiameter d oldRadius r.val-1≤radius r ∧
        radius r≤mixedEffectiveDiameter d oldRadius r.val-1+2*K) ∧
      (∀ r x,x∈Fnew.branch r → ∀ y,y∈Fnew.branch r →
        ∃ p : G.Walk x y,(∀ z∈p.support,z∈Fnew.branch r) ∧ walkWeight w p≤radius r) ∧
      (∀ t,t∉Q → ∃ x y,∃ p : H.Walk x y,p.IsPath ∧
        p.support.toFinset=ResidualComponents.block H (Finset.univ\roots) t ∧
          K≤pathMass (mixedEffectiveDiameter d oldRadius) p) ∧
      (∀ t,t∉Q → ∀ r,Disjoint (ResidualComponents.block H (Finset.univ\roots) t) (O.chosenFilled Q r)) ∧
      let oldEdges := C.connectorPool hA hT oldH holdH Subtype.val
      let newEdges := C0.connectorPool le_rfl hT (fun _ => C0.graph T) (fun _ => le_rfl) (O.chosenFilled Q)
      Disjoint oldEdges newEdges ∧
      (∑ e∈C.touchingEdges B (originalMixedLabels P ((Finset.univ\high).biUnion (O.chosenFilled Q))),w e)+
      (∑ e∈C.markedEdges B (originalMixedLabels P (high.biUnion (O.chosenFilled Q))),w e)+
      (∑ r,(c*radius r+future r))+
      (∑ i∈Finset.univ\Finset.univ.biUnion (O.chosenFilled Q),selectedResidualCredit P rootCredit credit i)≤
        (∑ i,originalCredit i)+c*(∑ e∈oldEdges∪newEdges,w e)

attribute [-instance] instDecidableEqSum in
 theorem paid_short_phase_output_of_inputs {I V : Type*} [Fintype I] [Fintype V]
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
    (hforest : H.IsAcyclic)
    (K c b M : ℝ) (spare future : {r // r∈selectedRoots P} → ℝ) (N q : ℕ)
    (hK : 0≤K) (hc : 0≤c) (hM : 0≤M)
    (hd0 : ∀ i,1≤d i)
    (hmax : ∀ W : Finset (SelectedResidualIndex P),ConnectedWithin H W → W⊆Finset.univ\selectedRoots P →
      (∃ x y,∃ p : H.Walk x y,p.IsPath ∧ (∀ i∈p.support,i∈W) ∧
        K≤pathMass (mixedEffectiveDiameter d oldRadius) p) →
          ∀ i∈W,((H.neighborFinset i)∩W).card≤2)
    (hcredit : ∀ i,i∉P.biUnion id → c*d i≤credit i)
    (hbase : ∀ i,i∉P.biUnion id → c*b≤credit i)
    (hdeg : ∀ i,i∉P.biUnion id → (C.graph B).degree i≤q)
    (hweight : ∀ e∈B.edgeSet,w e≤M)
    (hloop : ∀ i x,x∈C.branch i → ∀ y,y∈C.branch i → ¬B.Adj x y)
    (hsingle : ∀ i j x,x∈C.branch i → ∀ y,y∈C.branch j →
      ∀ u,u∈C.branch i → ∀ v,v∈C.branch j →
      B.Adj x y → B.Adj u v → s(x,y)=s(u,v))
    (hsize : 2*K≤N*b) (hrelease : (q:ℝ)*M≤c*b)
    (hbudget : ∀ r,N*((q:ℝ)*M)+future r≤spare r)
    (high : Finset {r // r∈selectedRoots P})
    (oldH : {S // S∈P} → SimpleGraph I) (holdH : ∀ S,oldH S≤C.graph T)
    (originalCredit : I → ℝ) (hw : ∀ e∈B.edgeSet,0≤w e)
    (hrootcredit : ∀ r,c*(mixedEffectiveDiameter d oldRadius r.val-1)+spare r≤
      selectedResidualCredit P rootCredit credit r.val)
    (hprior :
      (∑ e∈C.touchingEdges B (originalMixedLabels P ((Finset.univ\high).image Subtype.val)),w e)+
      (∑ e∈C.markedEdges B (originalMixedLabels P (high.image Subtype.val)),w e)+
      (∑ i,selectedResidualCredit P rootCredit credit i)≤(∑ i,originalCredit i)+
        c*(∑ e∈C.connectorPool hA hT oldH holdH Subtype.val,w e)) :
    PaidShortPhaseOutput (B:=B) C hA hT P F hbranch H d credit originalCredit oldRadius rootCredit
      K c high oldH holdH future := by
  unfold PaidShortPhaseOutput
  exact exists_paid_short_component_absorption C hcover hA hB hT hunit P hP F hbranch
    d credit oldRadius rootCredit hrad hC hF H hH hconn hforest K c b M spare future N q
    hK hc hM hd0 hmax hcredit hbase hdeg hweight hloop hsingle hsize hrelease hbudget
    high oldH holdH originalCredit hw hrootcredit hprior

end MinorFreeSpanners
