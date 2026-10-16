import LightEFTSpanners.NativeCycleBlocking

namespace LightEFTSpanners.NativeWeighted
open Finset
open scoped NNReal
variable {V E : Type*}
attribute [local instance] Classical.propDecidable

/-- Actual traced blockers and sampled native hosts with unrestricted
candidate-relative cycle exclusion. Full weighted girth still needs seed pruning. -/
theorem exists_traced_component_sample [Fintype V] [Fintype E]
    {G : Graph V E} {w : E → ℝ≥0} {H : Finset E} {q : ℕ}
    {T : Fin (q+1) → Finset E} (hb : SeedForestBudget G w H q T)
    (t : ℝ≥0) (f : ℕ) (hf : 0 < f) (es : List E) (hn : es.Nodup)
    (hsort : es.Pairwise (fun e d => w d ≤ w e))
    (hH : H ⊆ inputEdges G) (hinput : ∀ e ∈ es, e ∈ inputEdges G)
    (i : Fin (q+1)) (c : (G.restrict (T i : Set E)).toSimpleGraph.ConnectedComponent) :
    let U := nativeGreedy G w t f H es \ H
    ∃ block : E → Finset E, TracedBlockers G w t f H es block ∧
      let K := componentCandidates G (T i) (hostCandidates U T block i) c
      ∃ S R : Finset E, S ⊆ K ∧
        R = componentForest G (T i) c ∪ BlockerSampling.surviving K block S ∧
        R ⊆ inputEdges G ∧ componentForest G (T i) c ⊆ R ∧
        c.toSimpleGraph.IsTree ∧
        (totalWeight w K : ℝ) ≤ 4*(f:ℝ)*(totalWeight w R : ℝ) ∧
        (∀ u : G.vertexSet, ∀ p : Walk G R ∅ u u, p.edgeList.Nodup →
          ∀ d ∈ p.edgeList, d ∉ H → (t+1)*w d < p.weight w) := by
  classical
  dsimp only
  let U := nativeGreedy G w t f H es \ H
  obtain ⟨block,hblock,_⟩ := exists_traced_blockers G w t f H es hsort
  let K := componentCandidates G (T i) (hostCandidates U T block i) c
  have hU : U ⊆ inputEdges G \ H := by
    intro e he
    exact mem_sdiff.mpr ⟨nativeGreedy_input_containment G w t f H es hH hinput
      (mem_sdiff.mp he).1,(mem_sdiff.mp he).2⟩
  obtain ⟨S,R,hS,hR,hRI,hFR,htree,_,hclean,hweight⟩ := exists_sampled_component_host hb
    U hU block f hf (fun e he => (hblock.sampling e he).1)
    (fun e he => (hblock.sampling e he).2.1) i c
  have hK : K ⊆ U := (component_candidates_subset G (T i) _ c).trans (filter_subset _ _)
  have hFH : componentForest G (T i) c ⊆ H :=
    (component_candidates_subset G (T i) (T i) c).trans (hb.subset i)
  have hRG : R ⊆ nativeGreedy G w t f H es := by
    intro e he
    rw [hR] at he
    rcases mem_union.mp he with he | he
    · exact nativeGreedy_seed_subset G w t f H es (hFH he)
    · exact (mem_sdiff.mp (hK (mem_filter.mp he).1)).1
  have hclean' : ∀ e ∈ R, e ∉ H → Disjoint (block e) R := by
    intro e he hes
    rw [hR] at he
    rcases mem_union.mp he with he | he
    · exact False.elim (hes (hFH he))
    · exact hclean e he
  refine ⟨block,hblock,S,R,hS,hR,hRI,hFR,htree,hweight,?_⟩
  intro u p hp d hd hds
  exact hblock.clean_cycle hn hsort R hRG hclean' u p hp d hd hds

end LightEFTSpanners.NativeWeighted
