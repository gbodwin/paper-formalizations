import LightEFTSpanners.NativeGreedyBlocking

namespace LightEFTSpanners.NativeWeighted
open Finset
open scoped NNReal
variable {V E : Type*}
attribute [local instance] Classical.propDecidable

/-- A sampled component using blockers derived from actual greedy insertions.
Its cycle bound is relative to a newly bought edge and an earlier detour.
This deliberately does not assert full weighted girth of the raw host. -/
theorem exists_native_greedy_sample [Fintype V] [Fintype E]
    {G : Graph V E} {w : E → ℝ≥0} {H : Finset E} {q : ℕ}
    {T : Fin (q+1) → Finset E} (hb : SeedForestBudget G w H q T)
    (t : ℝ≥0) (f : ℕ) (hf : 0 < f) (es : List E)
    (hinput : nativeGreedy G w t f H es \ H ⊆ inputEdges G \ H)
    (i : Fin (q+1)) (c : (G.restrict (T i : Set E)).toSimpleGraph.ConnectedComponent) :
    let U := nativeGreedy G w t f H es \ H
    let D := nativeWitnessData G w t f H es
    let block := fun e => (D e).2
    let K := componentCandidates G (T i) (hostCandidates U T block i) c
    ∃ S R : Finset E, S ⊆ K ∧
      R = componentForest G (T i) c ∪ BlockerSampling.surviving K block S ∧
      R ⊆ inputEdges G ∧ componentForest G (T i) c ⊆ R ∧
      c.toSimpleGraph.IsTree ∧
      (totalWeight w K : ℝ) ≤ 4*(f:ℝ)*(totalWeight w R : ℝ) ∧
      (∀ e ∈ BlockerSampling.surviving K block S, ∀ x : G.vertexSet,
        ¬ G.IsLink e x.val x.val) ∧
      (∀ e ∈ BlockerSampling.surviving K block S, ∀ x y : G.vertexSet,
        G.IsLink e x.val y.val → ∀ p : Walk G (D e).1 ∅ x y,
        (∀ d ∈ p.edgeList, d ∈ R) → (t+1)*w e < p.weight w + w e) := by
  classical
  dsimp only
  let U := nativeGreedy G w t f H es \ H
  let D := nativeWitnessData G w t f H es
  let block := fun e => (D e).2
  let K := componentCandidates G (T i) (hostCandidates U T block i) c
  have hK : K ⊆ U := (component_candidates_subset G (T i) _ c).trans (filter_subset _ _)
  obtain ⟨S,R,hS,hR,hRI,hFR,htree,_,hclean,hweight⟩ := exists_sampled_component_host hb
    U hinput block f hf (fun e he => (nativeWitnessData_sampling G w t f H es e he).2.1)
    (fun e he => (nativeWitnessData_sampling G w t f H es e he).2.2) i c
  refine ⟨S,R,hS,hR,hRI,hFR,htree,hweight,?_,?_⟩
  · intro e he x
    exact nativeGreedy_no_new_loop G w t f H es e (hK (mem_filter.mp he).1) x
  · intro e he x y hl p hp
    exact (nativeWitnessData_spec G w t f H es e (hK (mem_filter.mp he).1)).2.clean_cycle_lt
      (hclean e he) hl p hp

end LightEFTSpanners.NativeWeighted
