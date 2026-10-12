import MinorFreeSpanners.UnabsorbedComponents
import MinorFreeSpanners.ResidualComponentIsoTransport
import MinorFreeSpanners.ExpandedRemainingIso

/-! Every remaining component of the next common tree has an actual long
spanning path. The path is transported from its exact unabsorbed predecessor,
with no new maximal-path oracle or small-total-mass hypothesis. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

attribute [-instance] instDecidableEqSum in
 theorem expanded_remaining_long_paths {I : Type*} [Fintype I]
    (P U : Finset (Finset I)) (H : SimpleGraph (SelectedResidualIndex P))
    (K : SimpleGraph (SelectedResidualIndex U)) (T : SimpleGraph I)
    (hH : ∀ i j : {i // i∉P.biUnion id},H.Adj (Sum.inr i) (Sum.inr j) ↔ T.Adj i.val j.val)
    (hK : ∀ i j : {i // i∉U.biUnion id},K.Adj (Sum.inr i) (Sum.inr j) ↔ T.Adj i.val j.val)
    (O : ResidualOwnership H (selectedRoots P))
    (Q : Finset (H.induce ((Finset.univ\selectedRoots P : Finset (SelectedResidualIndex P)):Set _)).ConnectedComponent)
    (hU : U.biUnion id=originalMixedLabels P (Finset.univ.biUnion (O.chosenFilled Q)))
    (d : I → ℝ) (oldRadius : {g // g∈P} → ℝ) (newRadius : {g // g∈U} → ℝ) (L : ℝ)
    (hlong : ∀ t,t∉Q → ∃ x y,∃ p : H.Walk x y,p.IsPath ∧
      p.support.toFinset=ResidualComponents.block H (Finset.univ\selectedRoots P) t ∧
      L≤pathMass (mixedEffectiveDiameter d oldRadius) p) :
    ∀ t : (K.induce ((Finset.univ\selectedRoots U : Finset (SelectedResidualIndex U)):Set _)).ConnectedComponent,
      ∃ x y,∃ p : K.Walk x y,p.IsPath ∧
        p.support.toFinset=ResidualComponents.block K (Finset.univ\selectedRoots U) t ∧
        L≤pathMass (mixedEffectiveDiameter d newRadius) p := by
  classical
  let W := Finset.univ.biUnion (O.chosenFilled Q)
  have hroot := chosenFilled_contains_roots O Q
  let e := expandedRemainingIso P U W hroot hU H K T hH hK
  apply ResidualComponents.all_spanning_paths_transport (Finset.univ\W) (Finset.univ\selectedRoots U)
    e (mixedEffectiveDiameter d oldRadius) (mixedEffectiveDiameter d newRadius)
    (expandedRemainingIso_mass P U W hroot hU H K T hH hK d oldRadius newRadius) L
  intro q
  obtain ⟨t,ht,he⟩ := O.unchosen_components Q q
  obtain ⟨x,y,p,hp,hs,hm⟩ := hlong t ht
  exact ⟨x,y,p,hp,hs.trans he.symm,hm⟩

end MinorFreeSpanners
