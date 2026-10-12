import MinorFreeSpanners.ExpandedRemainingLongPaths
import MinorFreeSpanners.SelectedResidualMaximality
import MinorFreeSpanners.ResidualMassDichotomy

/-! The same earlier branching maximality and the transported long paths
supply the full residual degree-two bound needed by actual path assembly. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

attribute [-instance] instDecidableEqSum in
 theorem expanded_remaining_degree_two {I : Type*} [Fintype I]
    (P U : Finset (Finset I)) (W : Finset (SelectedResidualIndex P))
    (hroot : selectedRoots P⊆W) (hU : U.biUnion id=originalMixedLabels P W)
    (K : SimpleGraph (SelectedResidualIndex U)) (T : SimpleGraph I)
    (hres : ∀ i j : {i // i∉U.biUnion id},K.Adj (Sum.inr i) (Sum.inr j) ↔ T.Adj i.val j.val)
    (d : I → ℝ) (radius : {g // g∈U} → ℝ) (L : ℝ)
    (hmax : ∀ S : Finset I,ConnectedWithin T S → Disjoint S (P.biUnion id) →
      (∃ x y,∃ p : T.Walk x y,p.IsPath ∧ (∀ i∈p.support,i∈S) ∧ L≤pathMass (fun i => d i+1) p) →
        ∀ i∈S,((T.neighborFinset i)∩S).card≤2)
    (hpath : ∀ t : (K.induce ((Finset.univ\selectedRoots U : Finset (SelectedResidualIndex U)):Set _)).ConnectedComponent,
      ∃ x y,∃ p : K.Walk x y,p.IsPath ∧
        p.support.toFinset=ResidualComponents.block K (Finset.univ\selectedRoots U) t ∧
        L≤pathMass (mixedEffectiveDiameter d radius) p) :
    ∀ i∉selectedRoots U,((K.neighborFinset i)\selectedRoots U).card≤2 := by
  classical
  have hPU : P.biUnion id⊆U.biUnion id := by
    intro i hi
    exact (Finset.ext_iff.mp hU i).mpr (old_selected_subset_expanded P W hroot hi)
  have hmaxU : ∀ S : Finset I,ConnectedWithin T S → Disjoint S (U.biUnion id) →
      (∃ x y,∃ p : T.Walk x y,p.IsPath ∧ (∀ i∈p.support,i∈S) ∧ L≤pathMass (fun i => d i+1) p) →
        ∀ i∈S,((T.neighborFinset i)∩S).card≤2 := by
    intro S hconn hdis hp
    exact hmax S hconn (hdis.mono_right hPU) hp
  have hmixed : ∀ S : Finset (SelectedResidualIndex U),ConnectedWithin K S →
      S⊆Finset.univ\selectedRoots U →
      (∃ x y,∃ p : K.Walk x y,p.IsPath ∧ (∀ i∈p.support,i∈S) ∧
        L≤pathMass (mixedEffectiveDiameter d radius) p) →
          ∀ i∈S,((K.neighborFinset i)∩S).card≤2 := by
    intro S hconn hS hp
    exact selected_residual_branching_maximality U K T hres d radius L hmaxU S hconn
      (fun i hi => (Finset.mem_sdiff.mp (hS hi)).2) hp
  intro i hi
  obtain ⟨t,hit⟩ := ResidualComponents.covers K (Finset.univ\selectedRoots U)
    (Finset.mem_sdiff.mpr ⟨mem_univ _,hi⟩)
  obtain ⟨x,y,p,hp,hs,hl⟩ := hpath t
  have ht : LongResidualComponent K (Finset.univ\selectedRoots U) (mixedEffectiveDiameter d radius) L t :=
    ⟨x,y,p,hp,fun i hi => hs ▸ List.mem_toFinset.mpr hi,hl⟩
  have hh := long_residual_component_degree K (Finset.univ\selectedRoots U)
    (mixedEffectiveDiameter d radius) L hmixed t ht i hit
  have he : (K.neighborFinset i)∩(Finset.univ\selectedRoots U)=(K.neighborFinset i)\selectedRoots U := by
    ext j
    simp
  rwa [he] at hh

end MinorFreeSpanners
