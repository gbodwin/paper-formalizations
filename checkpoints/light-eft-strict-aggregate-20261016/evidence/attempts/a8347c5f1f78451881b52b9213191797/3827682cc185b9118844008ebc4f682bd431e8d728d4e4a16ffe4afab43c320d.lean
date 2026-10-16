import LightEFTSpanners.NativeCorePackingCriterion
import LightEFTSpanners.NativeTreePacking
import LightEFTSpanners.NativeContractionForestJoin

namespace LightEFTSpanners.EvenSplitting
open MultigraphCuts SimpleGraph
variable {V E : Type*} [Fintype V] [Fintype E]
attribute [local instance] Classical.propDecidable

/-- The native minimal-core partition argument and the proved finite tree
packing theorem construct the core trees themselves. No tree family is supplied. -/
theorem exists_native_minimal_core_trees (G : Graph V E) (K : Finset V) (k : ℕ)
    (hne : K.Nonempty) (hactual : (K:Set V)⊆G.vertexSet)
    (hsmall : (G.edgeCut (K:Set V)).toFinset.card≤2*k)
    (hmin : ∀ A : Finset V,A⊂K → A.Nonempty →
      2*k≤(G.edgeCut (A:Set V)).toFinset.card) :
    ∃ T : Fin k → Set E,
      (∀ c,T c⊆(G.induce (K:Set V)).edgeSet ∧
        (∀ e∈((G.induce (K:Set V)).restrict (T c)).edgeSet,
          ((G.induce (K:Set V)).restrict (T c)).IsBridge e) ∧
        ((G.induce (K:Set V)).restrict (T c)).toSimpleGraph.Connected ∧
        Nat.card (T c)+1=Nat.card (K:Set V)) ∧
      Pairwise (fun c d => Disjoint (T c) (T d)) := by
  classical
  obtain ⟨x,hx⟩ := hne
  let : Nonempty (G.induce (K:Set V)).vertexSet := ⟨⟨x,hx⟩⟩
  let : Fintype (G.induce (K:Set V)).vertexSet := Fintype.ofFinite _
  exact exists_native_tree_packing (G.induce (K:Set V)) k
    (native_core_treePartitionCriterion G K hactual hsmall hmin).2

omit [Fintype V] [Fintype E] in
/-- An induced selected tree really connects its original vertices using the
same selected original edge identities in the full graph. -/
theorem induced_reachable_original (G : Graph V E) (K : Set V)
    (hactual : K⊆G.vertexSet) (T : Set E) {x y : K}
    (h : ((G.induce K).restrict T).toSimpleGraph.Reachable x y) :
    (G.restrict T).toSimpleGraph.Reachable ⟨x.val,hactual x.property⟩
      ⟨y.val,hactual y.property⟩ := by
  let f : ((G.induce K).restrict T).toSimpleGraph →g (G.restrict T).toSimpleGraph :=
    { toFun := fun a => ⟨a.val,hactual a.property⟩
      map_rel' := by
        rintro a b ⟨hne,e,he,hlink⟩
        exact ⟨fun h => hne (Subtype.ext (congrArg (fun z : G.vertexSet => z.val) h)),e,he,hlink.1⟩ }
  exact h.map f

omit [Fintype V] [Fintype E] in
/-- A connected induced core supplies all nontrivial fiber paths when that
core is contracted; every outside fiber is an actual singleton. -/
theorem core_tree_connects_collapse_fibers (G : Graph V E) (K : Set V)
    (hactual : K⊆G.vertexSet) (T : Set E)
    (hc : ((G.induce K).restrict T).toSimpleGraph.Connected)
    (x y : G.vertexSet) (hf : collapseOutside Kᶜ x.val=collapseOutside Kᶜ y.val) :
    (G.restrict T).toSimpleGraph.Reachable x y := by
  classical
  by_cases hx : x.val∈K
  · by_cases hy : y.val∈K
    · exact induced_reachable_original G K hactual T (hc.preconnected ⟨x.val,hx⟩ ⟨y.val,hy⟩)
    · simp [collapseOutside,hx,hy] at hf
  · by_cases hy : y.val∈K
    · simp [collapseOutside,hx,hy] at hf
    · have hxy : x=y := by
        simp only [collapseOutside,Set.mem_compl_iff,hx,hy,not_false_eq_true,dite_eq_left] at hf
        exact Subtype.ext (congrArg (fun z : ↥(Kᶜ) => z.val) (Option.some.inj hf))
      subst y; exact Reachable.rfl
end LightEFTSpanners.EvenSplitting
