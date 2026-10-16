import LightEFTSpanners.NativeForestExchange

namespace LightEFTSpanners.NativeWeighted
open Finset
open scoped NNReal
variable {V E : Type*}
attribute [local instance] Classical.propDecidable

/-- Full native weighted-girth exclusion on edge-simple closed walks, measured
against every cycle ID, not only newly bought IDs. Loops and parallel two-edge
cycles remain in the quantified domain. -/
def NativeWeightedGirthAbove (G : Graph V E) (R : Finset E) (w : E → ℝ≥0) (b : ℝ≥0) : Prop :=
  ∀ u : G.vertexSet, ∀ p : Walk G R ∅ u u, p.edgeList.Nodup →
    ∀ e ∈ p.edgeList, b * w e < p.weight w

/-- Construct a minimum native spanning forest and delete only seed IDs outside
it. The forest weight is bounded by any supplied spanning seed. Full girth is
derived from the already proved candidate-relative cycle exclusion, not assumed.
Disconnected ambient graphs and empty hosts are allowed. -/
theorem exists_native_seed_prune [DecidableEq E] (G : Graph V E) (w : E → ℝ≥0)
    (A seed T : Finset E) (b : ℝ≥0) (hT : NativeSpans G A T)
    (hcycle : ∀ u : G.vertexSet, ∀ p : Walk G A ∅ u u, p.edgeList.Nodup →
      ∀ e ∈ p.edgeList, e ∉ seed → b * w e < p.weight w) :
    ∃ K R : Finset E, NativeSpans G A K ∧ NativeForest G K ∧
      R = A \ (seed \ K) ∧ K ⊆ R ∧ R ⊆ A ∧ A \ seed ⊆ R ∧
      NativeSpans G A R ∧ totalWeight w K ≤ totalWeight w T ∧
      NativeWeightedGirthAbove G R w b := by
  classical
  obtain ⟨K,hK,hforest,hmin⟩ := exists_native_minimum_forest G w A
  let R := A \ (seed \ K)
  have hKR : K ⊆ R := by
    intro e he
    exact mem_sdiff.mpr ⟨hK.1 he,fun h => (mem_sdiff.mp h).2 he⟩
  have hRA : R ⊆ A := sdiff_subset
  have hnew : A \ seed ⊆ R := by
    intro e he
    exact mem_sdiff.mpr ⟨(mem_sdiff.mp he).1,fun h => (mem_sdiff.mp he).2 (mem_sdiff.mp h).1⟩
  refine ⟨K,R,hK,hforest,rfl,hKR,hRA,hnew,⟨hRA,fun u v h => (hK.2 u v h).mono hKR⟩,
    hmin T hT,?_⟩
  intro u p hp e he
  obtain ⟨s,hse,hsw⟩ := p.transfer_selected w A (fun d hd => hRA (p.edgeList_selected d hd))
  have hsn : s.edgeList.Nodup := hse.symm ▸ hp
  have hsne : s.edgeList ≠ [] := by
    intro h
    have he' : e ∈ s.edgeList := hse.symm ▸ he
    simp only [h,List.not_mem_nil] at he'
  obtain ⟨d,hd,hdK,hmax⟩ := native_cycle_maximum_outside hK hforest hmin s hsn hsne
  have hdR : d ∈ R := p.edgeList_selected d (hse ▸ hd)
  have hdseed : d ∉ seed := fun h => (mem_sdiff.mp hdR).2 (mem_sdiff.mpr ⟨h,hdK⟩)
  have hlt := hcycle u s hsn d hd hdseed
  rw [hsw] at hlt
  exact (mul_le_mul_of_nonneg_left (hmax e (hse.symm ▸ he)) (zero_le : 0 ≤ b)).trans_lt hlt

/-- The component forest connects its actual component vertices using original
IDs. No spanning assertion is made on unrelated ambient vertices. -/
theorem component_forest_reachable (G : Graph V E) (T : Finset E)
    (c : (G.restrict (T : Set E)).toSimpleGraph.ConnectedComponent)
    (hc : c.toSimpleGraph.Connected) (u v : c) :
    NativeReach G (componentForest G T c) u.val v.val := by
  obtain ⟨p⟩ := hc.preconnected u v
  induction p with
  | nil => exact .refl _
  | @cons u v z huv p ih =>
    obtain ⟨_,e,he,hl⟩ := (component_forest_adjacency G T c u v).mp huv
    exact (NativeReach.single hl he).trans ih

/-- Any host whose edge endpoints lie in this component is spanned by the
retained component forest. Empty walks outside the component are harmless. -/
theorem component_forest_spans (G : Graph V E) (T A : Finset E)
    (c : (G.restrict (T : Set E)).toSimpleGraph.ConnectedComponent)
    (hc : c.toSimpleGraph.Connected) (hF : componentForest G T c ⊆ A)
    (hends : ∀ e ∈ A, ∃ x y : G.vertexSet, G.IsLink e x.val y.val ∧ x ∈ c.supp ∧ y ∈ c.supp) :
    NativeSpans G A (componentForest G T c) := by
  refine ⟨hF,?_⟩
  intro u v huv
  apply native_reach_replace (A:=A) ?_ huv
  intro e he x y hl
  obtain ⟨a,b,hab,ha,hb⟩ := hends e he
  have hr := component_forest_reachable G T c hc ⟨a,ha⟩ ⟨b,hb⟩
  exact hr.same_link hab hl

/-- Instantiate the native pruning construction on the actual traced sampled
component host. Every sampled candidate ID survives; the retained spanning
forest costs at most the original component seed forest; full girth follows. -/
theorem exists_pruned_traced_component [Fintype V] [Fintype E]
    {G : Graph V E} {w : E → ℝ≥0} {H : Finset E} {q : ℕ}
    {T : Fin (q+1) → Finset E} (hb : SeedForestBudget G w H q T)
    (t : ℝ≥0) (f : ℕ) (hf : 0 < f) (es : List E) (hn : es.Nodup)
    (hsort : es.Pairwise (fun e d => w d ≤ w e))
    (hH : H ⊆ inputEdges G) (hinput : ∀ e ∈ es, e ∈ inputEdges G)
    (i : Fin (q+1)) (c : (G.restrict (T i : Set E)).toSimpleGraph.ConnectedComponent) :
    let U := nativeGreedy G w t f H es \ H
    ∃ block : E → Finset E, TracedBlockers G w t f H es block ∧
      let C := componentCandidates G (T i) (hostCandidates U T block i) c
      ∃ S A K R : Finset E, S ⊆ C ∧
        A = componentForest G (T i) c ∪ BlockerSampling.surviving C block S ∧
        A ⊆ inputEdges G ∧ NativeSpans G A K ∧ NativeForest G K ∧
        R = A \ (H \ K) ∧ K ⊆ R ∧ R ⊆ A ∧
        BlockerSampling.surviving C block S ⊆ R ∧ NativeSpans G A R ∧
        totalWeight w K ≤ totalWeight w (componentForest G (T i) c) ∧
        NativeWeightedGirthAbove G R w (t+1) ∧
        (totalWeight w C : ℝ) ≤ 4*(f:ℝ)*(totalWeight w A : ℝ) := by
  classical
  dsimp only
  let U := nativeGreedy G w t f H es \ H
  obtain ⟨block,hblock,S,A,hS,hA,hAI,hFA,htree,hweight,hcycle⟩ :=
    exists_traced_component_sample hb t f hf es hn hsort hH hinput i c
  let C := componentCandidates G (T i) (hostCandidates U T block i) c
  have hCU : C ⊆ U := (component_candidates_subset G (T i) _ c).trans (filter_subset _ _)
  have hends : ∀ e ∈ A, ∃ x y : G.vertexSet, G.IsLink e x.val y.val ∧ x ∈ c.supp ∧ y ∈ c.supp := by
    intro e he
    rw [hA] at he
    rcases mem_union.mp he with he | he
    · exact ((mem_componentCandidates G (T i) (T i) c e).mp he).2
    · exact ((mem_componentCandidates G (T i) _ c e).mp (mem_filter.mp he).1).2
  have hspan := component_forest_spans G (T i) A c htree.connected hFA hends
  obtain ⟨K,R,hK,hforest,hR,hKR,hRA,hnew,hspanR,hbudget,hgirth⟩ :=
    exists_native_seed_prune G w A H (componentForest G (T i) c) (t+1) hspan hcycle
  refine ⟨block,hblock,S,A,K,R,hS,hA,hAI,hK,hforest,hR,hKR,hRA,?_,hspanR,hbudget,hgirth,hweight⟩
  intro e he
  apply hnew
  refine mem_sdiff.mpr ⟨?_,(mem_sdiff.mp (hCU (mem_filter.mp he).1)).2⟩
  rw [hA]
  exact mem_union_right _ he

end LightEFTSpanners.NativeWeighted
