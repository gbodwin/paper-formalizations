import LightEFTSpanners.MinimalConnectivityCore
import LightEFTSpanners.MultigraphCutTransport

namespace LightEFTSpanners.MultigraphCuts
open SimpleGraph Finset
variable {V E : Type*}
attribute [local instance] Classical.propDecidable

/-- Complementing a vertex set preserves the actual unordered edge cut,
including loops and parallel edge identities in the native graph model. -/
theorem edgeCut_compl (G : Graph V E) (S : Set V) :
    G.edgeCut Sᶜ=G.edgeCut S := by
  ext e
  constructor
  · rintro ⟨u,v,h,hu,hv⟩
    exact ⟨v,u,h.symm,not_not.mp hv,hu⟩
  · rintro ⟨u,v,h,hu,hv⟩
    exact ⟨v,u,h.symm,hv,not_not.mpr hu⟩

/-- A target set avoiding the contracted outside vertex pulls back to a
subset of the retained core, with exact membership for each core vertex. -/
theorem collapse_preimage_subset (K : Set V) (S : Set (Option K))
    (hn : none∉S) : collapseOutside K ⁻¹' S⊆K := by
  intro v hv
  by_contra h
  exact hn (by simpa [collapseOutside,h] using hv)

theorem collapse_mem (K : Set V) (v : K) (S : Set (Option K)) :
    v.val∈collapseOutside K ⁻¹' S ↔ some v∈S := by
  simp [collapseOutside,v.property]

/-- The minimal deficient-core argument gives a real lower bound on every
separating cut after complement contraction. Edge identities are retained;
this is the cut obligation in CS09 Lemma 2.4, not an assumed packing theorem. -/
theorem minimal_core_contracted_cut_lower [Fintype V] (G : SimpleGraph V)
    (K : Finset V) {k : ℕ}
    (hmin : ∀ A : Finset V,A⊂K → A.Nonempty →
      k≤(ConnectivityCuts.edges G (A:Set V)).card)
    (a b : (K:Set V)) (S : Set (Option (K:Set V)))
    (ha : some a∈S) (hb : some b∉S) :
    k≤(((Graph.ofSimpleGraph G).map (collapseOutside (K:Set V))).edgeCut S).toFinset.card := by
  classical
  have hside (T : Set (Option (K:Set V))) (hn : none∉T)
      (x y : (K:Set V)) (hx : some x∈T) (hy : some y∉T) :
      k≤(((Graph.ofSimpleGraph G).map (collapseOutside (K:Set V))).edgeCut T).toFinset.card := by
    let A : Set V := collapseOutside (K:Set V) ⁻¹' T
    have hAK : A⊆(K:Set V) := collapse_preimage_subset _ _ hn
    have hxA : x.val∈A := (collapse_mem _ _ _).mpr hx
    have hyA : y.val∉A := fun h => hy ((collapse_mem _ _ _).mp h)
    have hsub : A.toFinset⊆K := by simpa using hAK
    have hne : A.toFinset≠K := by
      intro heq
      have hyK : y.val∈A.toFinset :=
        (congrArg (fun t : Finset V => y.val∈t) heq).mpr y.property
      exact hyA (by simpa using hyK)
    have hlower := hmin A.toFinset (lt_of_le_of_ne hsub hne)
      ⟨x.val,by simpa using hxA⟩
    rw [edgeCut_map,ofSimpleGraph_cut]
    simpa [A] using hlower
  by_cases hn : none∈S
  · have h := hside Sᶜ (by simpa using hn) b a hb (by simpa using ha)
    simpa only [edgeCut_compl] using h
  · exact hside S hn a b ha hb
end LightEFTSpanners.MultigraphCuts
