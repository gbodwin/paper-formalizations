import MinorFreeSpanners.ReindexedShortAbsorption
import MinorFreeSpanners.ExpandedRemainingDegree

/-! The actual short-output transition now supplies every complete long-path
and degree-two input on its new tree, alongside the same retained resource
ledger. Earlier branching maximality is reused on the smaller original domain. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

attribute [-instance] instDecidableEqSum in
 theorem reindex_paid_short_long_inputs {I V : Type*} [Fintype I] [Fintype V]
    {A B T G : SimpleGraph V} {w : Sym2 V → ℝ} {D E : ℝ}
    (C : ClusterFamily (I:=I) A w D) (hA : A≤G) (hT : T≤G)
    (P : Finset (Finset I)) (F : ClusterFamily (I:={S // S∈P}) G w E)
    (hbranch : ∀ S,F.branch S={x | ∃ i∈S.val,x∈C.branch i})
    (H : SimpleGraph (SelectedResidualIndex P)) (hHtree : H.IsTree)
    (hH : H≤(C.selectedResidual hA P F hbranch).graph T)
    (Horiginal : SimpleGraph I)
    (hprevious : ∀ i j : {i // i∉P.biUnion id},H.Adj (Sum.inr i) (Sum.inr j) ↔ Horiginal.Adj i.val j.val)
    (d credit originalCredit : I → ℝ) (oldRadius rootCredit : {S // S∈P} → ℝ)
    (K c : ℝ) (high : Finset {r // r∈selectedRoots P})
    (hmax : ∀ S : Finset I,ConnectedWithin Horiginal S → Disjoint S (P.biUnion id) →
      (∃ x y,∃ p : Horiginal.Walk x y,p.IsPath ∧ (∀ i∈p.support,i∈S) ∧
        K≤pathMass (fun i => d i+1) p) → ∀ i∈S,((Horiginal.neighborFinset i)∩S).card≤2)
    (oldH : {S // S∈P} → SimpleGraph I) (holdH : ∀ S,oldH S≤C.graph T)
    (future : {r // r∈selectedRoots P} → ℝ)
    (hshort : PaidShortPhaseOutput (B:=B) C hA hT P F hbranch H d credit originalCredit
      oldRadius rootCredit K c high oldH holdH future) :
    let C0 := C.selectedResidual hA P F hbranch
    ∃ Q : Finset (H.induce ((Finset.univ\selectedRoots P : Finset (SelectedResidualIndex P)):Set _)).ConnectedComponent,
    ∃ O : ResidualOwnership H (selectedRoots P),
    ∃ Fnew : ClusterFamily (I:={r // r∈selectedRoots P}) G w (E+2*K),
    ∃ radius : {r // r∈selectedRoots P} → ℝ,
    ∃ U : Finset (Finset I),∃ e : {r // r∈selectedRoots P} ≃ {g // g∈U},
      (∀ t,t∈Q ↔ ¬LongResidualComponent H (Finset.univ\selectedRoots P)
        (mixedEffectiveDiameter d oldRadius) K t) ∧
      (∀ r,Fnew.branch r={x | ∃ i∈O.chosenFilled Q r,x∈C0.branch i}) ∧
      (∀ r,(e r).val=originalMixedLabels P (O.chosenFilled Q r)) ∧
      (∀ r,mixedEffectiveDiameter d oldRadius r.val-1≤radius r ∧
        radius r≤mixedEffectiveDiameter d oldRadius r.val-1+2*K) ∧
      (∀ r x,x∈Fnew.branch r → ∀ y,y∈Fnew.branch r →
        ∃ p : G.Walk x y,(∀ z∈p.support,z∈Fnew.branch r) ∧ walkWeight w p≤radius r) ∧
      (∀ t,t∉Q → ∃ x y,∃ p : H.Walk x y,p.IsPath ∧
        p.support.toFinset=ResidualComponents.block H (Finset.univ\selectedRoots P) t ∧
          K≤pathMass (mixedEffectiveDiameter d oldRadius) p) ∧
      (∀ t,t∉Q → ∀ r,Disjoint (ResidualComponents.block H (Finset.univ\selectedRoots P) t) (O.chosenFilled Q r)) ∧
      U.biUnion id=originalMixedLabels P (Finset.univ.biUnion (O.chosenFilled Q)) ∧
      ∃ hfinal : ∀ g,(Fnew.reindex e.symm).branch g={x | ∃ i∈g.val,x∈C.branch i},
      ∃ Hnew : SimpleGraph (SelectedResidualIndex U),
        Hnew≤(C.selectedResidual hA U (Fnew.reindex e.symm) hfinal).graph T ∧ Hnew.IsTree ∧
        (∀ i j : {i // i∉U.biUnion id},Hnew.Adj (Sum.inr i) (Sum.inr j) ↔
          Horiginal.Adj i.val j.val) ∧
        let prior := C.connectorPool hA hT oldH holdH Subtype.val ∪
          C0.connectorPool le_rfl hT (fun _ : {r // r∈selectedRoots P} => C0.graph T)
            (fun _ => le_rfl) (O.chosenFilled Q)
        (∀ f∈prior,f∈T.edgeSet) ∧
        (∀ f∈prior,∃ g x y,x∈(Fnew.reindex e.symm).branch g ∧
          y∈(Fnew.reindex e.symm).branch g ∧ f=s(x,y)) ∧
        (∑ f∈C.touchingEdges B ((Finset.univ\high.image e).biUnion Subtype.val),w f)+
        (∑ f∈C.markedEdges B ((high.image e).biUnion Subtype.val),w f)+
        (∑ i,selectedResidualCredit U (fun g => c*radius (e.symm g)+future (e.symm g)) credit i)≤
          (∑ i,originalCredit i)+c*(∑ f∈prior,w f) ∧
        (∀ i∉selectedRoots U,((Hnew.neighborFinset i)\selectedRoots U).card≤2) ∧
        (∀ t : (Hnew.induce ((Finset.univ\selectedRoots U : Finset (SelectedResidualIndex U)):Set _)).ConnectedComponent,
          ∃ x y,∃ p : Hnew.Walk x y,p.IsPath ∧
            p.support.toFinset=ResidualComponents.block Hnew (Finset.univ\selectedRoots U) t ∧
            K≤pathMass (mixedEffectiveDiameter d (fun g => radius (e.symm g))) p) ∧
        (∀ t : (Hnew.induce ((Finset.univ\selectedRoots U : Finset (SelectedResidualIndex U)):Set _)).ConnectedComponent,
          K≤∑ i∈ResidualComponents.block Hnew (Finset.univ\selectedRoots U) t,
            mixedEffectiveDiameter d (fun g => radius (e.symm g)) i) := by
  classical
  intro C0
  obtain ⟨Q,O,Fnew,radius,U,e,hQ,hnew,he,hrad,hdiam,hlong,hdis,hU,hfinal,Hnew,
    hHnew,hTree,hres,hpriorT,hpriorInternal,hpaid⟩ := reindex_paid_short_absorption C hA hT P F hbranch
      H hHtree hH Horiginal hprevious d credit originalCredit oldRadius rootCredit K c high oldH holdH future hshort
  have hpaths := expanded_remaining_long_paths P U H Hnew Horiginal hprevious hres O Q hU
    d oldRadius (fun g => radius (e.symm g)) K hlong
  have hdeg := expanded_remaining_degree_two P U (Finset.univ.biUnion (O.chosenFilled Q))
    (chosenFilled_contains_roots O Q) hU Hnew Horiginal hres d (fun g => radius (e.symm g)) K hmax hpaths
  refine ⟨Q,O,Fnew,radius,U,e,hQ,hnew,he,hrad,hdiam,hlong,hdis,hU,hfinal,Hnew,
    hHnew,hTree,hres,hpriorT,hpriorInternal,hpaid,hdeg,hpaths,?_⟩
  intro t
  obtain ⟨x,y,p,_,hs,hm⟩ := hpaths t
  simpa only [pathMass,hs] using hm

end MinorFreeSpanners
