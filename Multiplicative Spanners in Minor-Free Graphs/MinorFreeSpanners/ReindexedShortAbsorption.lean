import MinorFreeSpanners.ExpandedResidualTree
import MinorFreeSpanners.ExpandedRetainedLedger
import MinorFreeSpanners.RetainedConnectorInternality
import MinorFreeSpanners.PaidShortPhaseOutput

/-! The same actual short-absorption witnesses now form a next original-label
cluster family with one residual-preserving tree and the unchanged paid ledger.
Every earlier connector stays literal and becomes internal to one next root. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

attribute [-instance] instDecidableEqSum in
 theorem reindex_paid_short_absorption {I V : Type*} [Fintype I] [Fintype V]
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
          (∑ i,originalCredit i)+c*(∑ f∈prior,w f) := by
  classical
  intro C0
  unfold PaidShortPhaseOutput at hshort
  obtain ⟨Q,O,Fnew,radius,hQ,hnew,_,hrad,hdiam,hlong,hdis,_,hpaid⟩ := hshort
  let S := O.chosenFilled Q
  let U := Finset.univ.image (fun r => originalMixedLabels P (S r))
  obtain ⟨e,he,hfinal,_,hU⟩ := C.expanded_original_groups hA P F hbranch S Fnew hnew
  have hroot := chosenFilled_contains_roots O Q
  obtain ⟨Hnew,hHnew,hHnewTree,hres⟩ := C.exists_expanded_residual_tree hA P F hbranch
    S hroot Fnew hnew U hU e hfinal H hHtree hH
  refine ⟨Q,O,Fnew,radius,U,e,hQ,hnew,he,hrad,hdiam,hlong,hdis,hU,hfinal,Hnew,
    hHnew,hHnewTree,?_,?_,?_,?_⟩
  · intro i j
    exact (hres i j).trans (hprevious _ _)
  · intro f hf
    rcases Finset.mem_union.mp hf with hf|hf
    · exact C.connectorPool_mem hA hT oldH holdH Subtype.val hf
    · exact C0.connectorPool_mem le_rfl hT (fun _ => C0.graph T) (fun _ => le_rfl) S hf
  · exact Fnew.reindex_internal_edges e _
      (C.absorbed_connector_union_internal hA hT P F hbranch H O Q Fnew hnew oldH holdH)
  · apply C.reindex_expanded_paid_ledger P U S hroot hU e he high rootCredit credit
      (fun r => c*radius r+future r)
    exact hpaid

end MinorFreeSpanners
