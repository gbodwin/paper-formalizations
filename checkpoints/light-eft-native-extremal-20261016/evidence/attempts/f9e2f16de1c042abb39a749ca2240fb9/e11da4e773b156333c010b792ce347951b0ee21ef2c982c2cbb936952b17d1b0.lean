import LightEFTSpanners.NativeWeightTransport

namespace LightEFTSpanners.NativeWeighted
open Finset SimpleGraph
open scoped NNReal
variable {V E : Type*}
attribute [local instance] Classical.propDecidable

/-- The native pruned host is bounded using its actual component cardinality,
then the established exact-order extremal monotonicity. All weights may be zero. -/
theorem native_component_extremal [Fintype V] (G : Graph V E) (w : E → ℝ≥0)
    (T R K : Finset E) (c : (G.restrict (T : Set E)).toSimpleGraph.ConnectedComponent)
    (hKR : K ⊆ R) (hK : (((G.restrict (K : Set E)).toSimpleGraph).induce c.supp).IsTree)
    (hends : ∀ e ∈ R, ∃ x y : G.vertexSet, G.IsLink e x.val y.val ∧ x ∈ c.supp ∧ y ∈ c.supp)
    (b : ℝ≥0) (hb : 2 < b) (hg : NativeWeightedGirthAbove G R w b) :
    (totalWeight w R : ℝ) ≤ extremalLightness (Fintype.card V) (b:ℝ) * (totalWeight w K : ℝ) := by
  classical
  let : Nonempty c := hK.connected.nonempty
  let j : c ↪ G.vertexSet := ⟨Subtype.val,Subtype.val_injective⟩
  have he : ∀ e ∈ R, ∃ u v : c, G.IsLink e (j u).val (j v).val := by
    intro e he
    obtain ⟨x,y,hl,hx,hy⟩ := hends e he
    exact ⟨⟨x,hx⟩,⟨y,hy⟩,hl⟩
  let M := nativeSimpleModel G R j (hg.simple hb.le) he
  have hproj : M.project K = ((G.restrict (K : Set E)).toSimpleGraph).induce c.supp := by
    ext u v
    rw [M.project_adj hKR]
    constructor
    · rintro ⟨hne,e,he,hl⟩
      exact ⟨fun h => hne (Subtype.ext h),e,he,hl⟩
    · rintro ⟨hne,e,he,hl⟩
      exact ⟨fun h => hne (congrArg Subtype.val h),e,he,hl⟩
  have hcard : Fintype.card c ≤ Fintype.card V :=
    Fintype.card_le_of_injective (fun u : c => u.val.val)
      (Subtype.val_injective.comp Subtype.val_injective)
  exact M.extremal_bound w K hKR (hproj.symm ▸ hK) b hb hg _ hcard

/-- A fixed traced blocker family is used for every component, so later sums
and candidate multiplicities refer to one assignment, not component-dependent
choices. The additive pruning loss remains the +1 in the coefficient. -/
theorem native_assigned_component_bound [Fintype V] [Fintype E]
    {G : Graph V E} {w : E → ℝ≥0} {H : Finset E} {q : ℕ}
    {T : Fin (q+1) → Finset E} (hb : SeedForestBudget G w H q T)
    (t : ℝ≥0) (ht : 2 < t+1) (f : ℕ) (hf : 0 < f) (es : List E) (hn : es.Nodup)
    (hsort : es.Pairwise (fun e d => w d ≤ w e))
    (hH : H ⊆ inputEdges G) (hinput : ∀ e ∈ es, e ∈ inputEdges G)
    (block : E → Finset E) (hblock : TracedBlockers G w t f H es block)
    (i : Fin (q+1)) (c : (G.restrict (T i : Set E)).toSimpleGraph.ConnectedComponent) :
    (totalWeight w (componentCandidates G (T i)
      (hostCandidates (nativeGreedy G w t f H es \ H) T block i) c) : ℝ) ≤
      4*(f:ℝ)*(extremalLightness (Fintype.card V) ((t+1:ℝ≥0):ℝ)+1)*
        (totalWeight w (componentForest G (T i) c) : ℝ) := by
  classical
  let U := nativeGreedy G w t f H es \ H
  let C := componentCandidates G (T i) (hostCandidates U T block i) c
  let F := componentForest G (T i) c
  have hU : U ⊆ inputEdges G \ H := by
    intro e he
    exact mem_sdiff.mpr ⟨nativeGreedy_input_containment G w t f H es hH hinput
      (mem_sdiff.mp he).1,(mem_sdiff.mp he).2⟩
  obtain ⟨S,A,hS,hA,hAI,hFA,htree,hends,hclean,hweight⟩ := exists_sampled_component_host hb
    U hU block f hf (fun e he => (hblock.sampling e he).1)
    (fun e he => (hblock.sampling e he).2.1) i c
  have hCU : C ⊆ U := (component_candidates_subset G (T i) _ c).trans (filter_subset _ _)
  have hFH : F ⊆ H := (component_candidates_subset G (T i) (T i) c).trans (hb.subset i)
  have hAG : A ⊆ nativeGreedy G w t f H es := by
    intro e he
    rw [hA] at he
    rcases mem_union.mp he with he | he
    · exact nativeGreedy_seed_subset G w t f H es (hFH he)
    · exact (mem_sdiff.mp (hCU (mem_filter.mp he).1)).1
  have hclean' : ∀ e ∈ A, e ∉ H → Disjoint (block e) A := by
    intro e he hes
    rw [hA] at he
    rcases mem_union.mp he with he | he
    · exact False.elim (hes (hFH he))
    · exact hclean e he
  have hcycle := hblock.clean_cycle hn hsort A hAG hclean'
  have hspan := component_forest_spans G (T i) A c htree.connected hFA hends
  obtain ⟨K,R,hK,hforest,hR,hKR,hRA,hnew,hspanR,hbudget,hgirth⟩ :=
    exists_native_seed_prune G w A H F (t+1) hspan hcycle
  have hKT := component_selected_tree G (T i) A K c htree.connected hFA hK hforest hends
  have hnative := native_component_extremal G w (T i) R K c hKR hKT
    (fun e he => hends e (hRA he)) (t+1) ht hgirth
  have hsurvive : BlockerSampling.surviving C block S ⊆ R := by
    intro e he
    apply hnew
    refine mem_sdiff.mpr ⟨?_,(mem_sdiff.mp (hCU (mem_filter.mp he).1)).2⟩
    rw [hA]
    exact mem_union_right _ he
  have hcover : A ⊆ R ∪ F := by
    intro e he
    rw [hA] at he
    rcases mem_union.mp he with he | he
    · exact mem_union_right _ he
    · exact mem_union_left _ (hsurvive he)
  have hloss : (totalWeight w A : ℝ) ≤ (totalWeight w R : ℝ) + (totalWeight w F : ℝ) := by
    exact_mod_cast native_weight_cover w A R F hcover
  have hbudget' : (totalWeight w K : ℝ) ≤ (totalWeight w F : ℝ) := by exact_mod_cast hbudget
  have hL := extremalLightness_nonneg (Fintype.card V) (show (2:ℝ) < ((t+1:ℝ≥0):ℝ) by exact_mod_cast ht)
  have hupper := hnative.trans (mul_le_mul_of_nonneg_left hbudget' hL)
  change (totalWeight w C : ℝ) ≤ _
  nlinarith

/-- Sum exact component partitions, then the native seed-forest weight budget.
The additive pruning loss is retained as L+1 throughout this aggregation. -/
theorem native_assigned_extremal_aggregate [Fintype V] [Fintype E]
    {G : Graph V E} {w : E → ℝ≥0} {H : Finset E} {q : ℕ}
    {T : Fin (q+1) → Finset E} (hb : SeedForestBudget G w H q T)
    (t : ℝ≥0) (ht : 2 < t+1) (f : ℕ) (hf : 0 < f) (es : List E) (hn : es.Nodup)
    (hsort : es.Pairwise (fun e d => w d ≤ w e))
    (hH : H ⊆ inputEdges G) (hinput : ∀ e ∈ es, e ∈ inputEdges G)
    (block : E → Finset E) (hblock : TracedBlockers G w t f H es block) :
    (∑ i, (totalWeight w (hostCandidates (nativeGreedy G w t f H es \ H) T block i) : ℝ)) ≤
      8*(f:ℝ)*(extremalLightness (Fintype.card V) ((t+1:ℝ≥0):ℝ)+1)*(totalWeight w H : ℝ) := by
  classical
  let U := nativeGreedy G w t f H es \ H
  let L := extremalLightness (Fintype.card V) ((t+1:ℝ≥0):ℝ)
  have hL : 0 ≤ L := extremalLightness_nonneg _ (by exact_mod_cast ht)
  have hc : 0 ≤ 4*(f:ℝ)*(L+1) := by positivity
  have hU : U ⊆ inputEdges G \ H := by
    intro e he
    exact mem_sdiff.mpr ⟨nativeGreedy_input_containment G w t f H es hH hinput
      (mem_sdiff.mp he).1,(mem_sdiff.mp he).2⟩
  have hi : ∀ i, (totalWeight w (hostCandidates U T block i) : ℝ) ≤
      4*(f:ℝ)*(L+1)*(totalWeight w (T i) : ℝ) := by
    intro i
    have heq : (∑ c, (totalWeight w (componentCandidates G (T i) (hostCandidates U T block i) c) : ℝ)) =
        (totalWeight w (hostCandidates U T block i) : ℝ) := by
      exact_mod_cast sum_component_candidate_weights hb U hU block i
    rw [← heq]
    calc
      _ ≤ ∑ c, 4*(f:ℝ)*(L+1)*(totalWeight w (componentForest G (T i) c) : ℝ) :=
        sum_le_sum (fun c _ => native_assigned_component_bound hb t ht f hf es hn hsort hH hinput block hblock i c)
      _ = 4*(f:ℝ)*(L+1)*(∑ c, (totalWeight w (componentForest G (T i) c) : ℝ)) := by rw [mul_sum]
      _ ≤ 4*(f:ℝ)*(L+1)*(totalWeight w (T i) : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast sum_component_forest_weights_le G w (T i)) hc
  have hsum := sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin (q+1)))) => hi i)
  rw [← mul_sum] at hsum
  have hbudget : (∑ i, (totalWeight w (T i) : ℝ)) ≤ 2*(totalWeight w H : ℝ) := by exact_mod_cast hb.weight_le
  have h := hsum.trans (mul_le_mul_of_nonneg_left hbudget hc)
  convert h using 1; ring

/-- Multiplicity charging with the additive loss still visible; no division
by h or by the seed weight, so zero-budget boundary cases remain valid. -/
theorem native_candidate_extremal_charge [Fintype V] [Fintype E]
    {G : Graph V E} {w : E → ℝ≥0} {H : Finset E} {q : ℕ}
    {T : Fin (q+1) → Finset E} (hb : SeedForestBudget G w H q T)
    (t : ℝ≥0) (ht : 2 < t+1) (f h : ℕ) (hf : 0 < f) (hcount : 2*f+h ≤ q+1)
    (es : List E) (hn : es.Nodup) (hsort : es.Pairwise (fun e d => w d ≤ w e))
    (hH : H ⊆ inputEdges G) (hinput : ∀ e ∈ es, e ∈ inputEdges G) :
    (h:ℝ)*(totalWeight w (nativeGreedy G w t f H es \ H) : ℝ) ≤
      8*(f:ℝ)*(extremalLightness (Fintype.card V) ((t+1:ℝ≥0):ℝ)+1)*(totalWeight w H : ℝ) := by
  obtain ⟨block,hblock,_⟩ := exists_traced_blockers G w t f H es hsort
  have hm := candidate_weight_multiplicity w (nativeGreedy G w t f H es \ H) T block f h
    (by simpa using hcount) (fun e he => (hblock.sampling e he).1) hb.congestion
  exact hm.trans (native_assigned_extremal_aggregate hb t ht f hf es hn hsort hH hinput block hblock)

end LightEFTSpanners.NativeWeighted
