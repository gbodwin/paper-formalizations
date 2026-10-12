import MinorFreeSpanners.SelectedResidualMaximality
import MinorFreeSpanners.ResidualLargeDomain

/-! The same mixed tree produced by the selected phases supplies its actual
small/large residual partition. The small side has bounded path mass; each
long-side component has a genuine long spanning path. Root reserves and
paid-label provenance are untouched by this geometric decomposition. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

attribute [-instance] instDecidableEqSum in
 theorem exists_selected_residual_mass_domains {I : Type*} [Fintype I]
    (P : Finset (Finset I)) (K : SimpleGraph (SelectedResidualIndex P)) (H : SimpleGraph I)
    (hK : K.IsAcyclic)
    (hres : ∀ i j : {i // i∉P.biUnion id},K.Adj (Sum.inr i) (Sum.inr j) ↔ H.Adj i.val j.val)
    (d : I → ℝ) (hd : ∀ i,1≤d i) (radius : {S // S∈P} → ℝ) (L : ℝ)
    (hmax : ∀ W : Finset I,ConnectedWithin H W → Disjoint W (P.biUnion id) →
      (∃ x y,∃ p : H.Walk x y,p.IsPath ∧ (∀ i∈p.support,i∈W) ∧ L≤pathMass (fun i => d i+1) p) →
        ∀ i∈W,((H.neighborFinset i)∩W).card≤2) :
    ∃ U S : Finset (SelectedResidualIndex P),
      U⊆Finset.univ\selectedRoots P ∧ S⊆Finset.univ\selectedRoots P ∧
      Disjoint U S ∧ U∪S=Finset.univ\selectedRoots P ∧
      (∀ i∈U,((K.neighborFinset i)∩U).card≤2) ∧
      (∀ t : (K.induce (U:Set _)).ConnectedComponent,
        ∃ x y,∃ p : K.Walk x y,p.IsPath ∧ p.support.toFinset=ResidualComponents.block K U t ∧
          L≤pathMass (mixedEffectiveDiameter d radius) p) ∧
      (∀ t : (K.induce (S:Set _)).ConnectedComponent,
        ∀ x y,∀ p : K.Walk x y,p.IsPath →
          (∀ i∈p.support,i∈ResidualComponents.block K S t) →
            pathMass (mixedEffectiveDiameter d radius) p<L) ∧
      (∀ i∈U,∀ j∈S,¬K.Adj i j) := by
  classical
  let R := Finset.univ\selectedRoots P
  have hdR : ∀ i∈R,0≤mixedEffectiveDiameter d radius i := by
    intro i hi
    have hn := (Finset.mem_sdiff.mp hi).2
    cases i with
    | inl t => exact (hn (by simp [selectedRoots])).elim
    | inr i => change 0≤d i.val+1;linarith [hd i.val]
  have hbranch : ∀ W : Finset (SelectedResidualIndex P),ConnectedWithin K W → W⊆R →
      (∃ x y,∃ p : K.Walk x y,p.IsPath ∧ (∀ i∈p.support,i∈W) ∧
        L≤pathMass (mixedEffectiveDiameter d radius) p) →
          ∀ i∈W,((K.neighborFinset i)∩W).card≤2 := by
    intro W hc hW hl
    exact selected_residual_branching_maximality P K H hres d radius L hmax W hc
      (fun i hi => (Finset.mem_sdiff.mp (hW hi)).2) hl
  obtain ⟨F,hU,hS,hdis,hcover,hdeg,hlong,hshort,hUc,hSc,hsep⟩ :=
    exists_residual_mass_domains K hK R (mixedEffectiveDiameter d radius) L hdR hbranch
  refine ⟨F.biUnion (ResidualComponents.block K R),
    (Finset.univ\F).biUnion (ResidualComponents.block K R),hU,hS,hdis,hcover,hdeg,?_,?_,hsep⟩
  · intro t
    obtain ⟨q,hq,he⟩ := hUc t
    obtain ⟨x,y,p,hp,hps,hm⟩ := hlong q hq
    exact ⟨x,y,p,hp,hps.trans he.symm,hm⟩
  · intro t x y p hp hs
    obtain ⟨q,hq,he⟩ := hSc t
    exact hshort q hq x y p hp (fun i hi => he ▸ hs i hi)

end MinorFreeSpanners
