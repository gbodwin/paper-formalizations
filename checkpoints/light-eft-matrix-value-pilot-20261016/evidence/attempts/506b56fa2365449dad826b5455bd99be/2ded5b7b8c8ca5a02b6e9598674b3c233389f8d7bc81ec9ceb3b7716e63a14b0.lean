import LightEFTSpanners.NativeCandidateAssignments
import LightEFTSpanners.NativeSeedPositivity
import LightEFTSpanners.WeightedSampling

namespace LightEFTSpanners.NativeWeighted
open Finset SimpleGraph
open scoped NNReal
variable {V E : Type*}
attribute [local instance] Classical.propDecidable

/-- Original forest IDs internal to one actual component. -/
noncomputable def componentForest (G : Graph V E) (T : Finset E)
    (c : (G.restrict (T : Set E)).toSimpleGraph.ConnectedComponent) : Finset E :=
  componentCandidates G T T c

/-- The component tree's adjacency is represented by these original IDs.
The component vertex subtype is used; no spanning claim is made on all V. -/
theorem component_forest_adjacency (G : Graph V E) (T : Finset E)
    (c : (G.restrict (T : Set E)).toSimpleGraph.ConnectedComponent) (u v : c) :
    c.toSimpleGraph.Adj u v ↔ u ≠ v ∧
      ∃ e ∈ componentForest G T c, G.IsLink e u.val.val v.val.val := by
  constructor
  · intro huv
    obtain ⟨hne,e,he,hl⟩ := huv
    refine ⟨fun h => hne (congrArg Subtype.val h),e,?_,hl⟩
    exact (mem_componentCandidates G T T c e).mpr ⟨he,u.val,v.val,hl,u.property,v.property⟩
  · rintro ⟨hne,e,he,hl⟩
    exact ⟨fun h => hne (Subtype.ext h),e,((mem_componentCandidates G T T c e).mp he).1,hl⟩

/-- Component seed weights do not duplicate original IDs. Even if T includes
unused ambient IDs, the actual component forests cost no more than T. -/
theorem sum_component_forest_weights_le [Fintype V] (G : Graph V E)
    (w : E → ℝ≥0) (T : Finset E) :
    (∑ c, totalWeight w (componentForest G T c)) ≤ totalWeight w T := by
  classical
  let C := componentForest G T
  have hc (e) : (HostCounting.hosts univ C e).card ≤ 1 := by
    apply card_le_one.mpr
    intro c hce d hde
    exact component_candidate_unique G T T (mem_filter.mp hce).2 (mem_filter.mp hde).2
  have hr : (∑ c, ∑ e ∈ C c, (w e : ℝ)) ≤ ∑ e ∈ T, (w e : ℝ) := by
    rw [HostCounting.weighted_incidence univ T C (fun e => (w e : ℝ))
      (fun c _ => component_candidates_subset G T T c)]
    apply sum_le_sum
    intro e _
    have hh : ((HostCounting.hosts univ C e).card : ℝ) ≤ 1 := by exact_mod_cast hc e
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hh (NNReal.coe_nonneg _)
  unfold totalWeight
  exact_mod_cast hr

/-- A component-local sampled native host retaining its original-ID forest.
This proves the sampling-weight step, not the remaining high-girth/host-upper
bound. Blocker sets are explicit; no final weighted estimate is a premise. -/
theorem exists_sampled_component_host [Fintype V] [Fintype E]
    {G : Graph V E} {w : E → ℝ≥0} {H : Finset E} {q : ℕ}
    {T : Fin (q+1) → Finset E} (hb : SeedForestBudget G w H q T)
    (U : Finset E) (hU : U ⊆ inputEdges G \ H) (block : E → Finset E)
    (f : ℕ) (hf : 0 < f) (hcap : ∀ e ∈ U, (block e).card ≤ f)
    (hself : ∀ e ∈ U, e ∉ block e) (i : Fin (q+1))
    (c : (G.restrict (T i : Set E)).toSimpleGraph.ConnectedComponent) :
    let K := componentCandidates G (T i) (hostCandidates U T block i) c
    ∃ (S R : Finset E), S ⊆ K ∧
      R = componentForest G (T i) c ∪ BlockerSampling.surviving K block S ∧
      R ⊆ inputEdges G ∧ componentForest G (T i) c ⊆ R ∧
      c.toSimpleGraph.IsTree ∧
      (∀ e ∈ R, ∃ u v : G.vertexSet, G.IsLink e u.val v.val ∧ u ∈ c.supp ∧ v ∈ c.supp) ∧
      (∀ e ∈ BlockerSampling.surviving K block S, Disjoint (block e) R) ∧
      (totalWeight w K : ℝ) ≤ 4*(f:ℝ)*(totalWeight w R : ℝ) := by
  classical
  dsimp only
  let A := hostCandidates U T block i
  let K := componentCandidates G (T i) A c
  let F := componentForest G (T i) c
  have hKA : K ⊆ A := component_candidates_subset G (T i) A c
  have hAU : A ⊆ U := filter_subset _ _
  have hKU : K ⊆ U := hKA.trans hAU
  obtain ⟨S,hSK,hweight⟩ := BlockerSampling.exists_heavy_surviving_sample K block
    (fun e => (w e : ℝ)) (fun _ _ => NNReal.coe_nonneg _) f hf
    (fun e he => hcap e (hKU he)) (fun e he => hself e (hKU he))
  let Q := BlockerSampling.surviving K block S
  let R := F ∪ Q
  have hQK : Q ⊆ K := filter_subset _ _
  have hFT : F ⊆ T i := component_candidates_subset G (T i) (T i) c
  refine ⟨S,R,hSK,rfl,?_,subset_union_left,host_component_tree hb i c,?_,?_,?_⟩
  · intro e he
    rcases mem_union.mp he with he | he
    · obtain ⟨_,u,v,hl,_,_⟩ := (mem_componentCandidates G (T i) (T i) c e).mp he
      exact Set.mem_toFinset.mpr hl.edge_mem
    · exact (mem_sdiff.mp (hU (hKU (hQK he)))).1
  · intro e he
    rcases mem_union.mp he with he | he
    · exact ((mem_componentCandidates G (T i) (T i) c e).mp he).2
    · exact ((mem_componentCandidates G (T i) A c e).mp (hQK he)).2
  · intro e he
    obtain ⟨heK,heS,hdis⟩ := mem_filter.mp he
    have hhost := (mem_filter.mp (hKA heK)).2
    apply Finset.disjoint_left.mpr
    intro d hd hdR
    rcases mem_union.mp hdR with hdF | hdQ
    · exact Finset.disjoint_left.mp hhost (hFT hdF) hd
    · obtain ⟨hdK,hdS,_⟩ := mem_filter.mp hdQ
      exact Finset.disjoint_left.mp hdis (mem_inter.mpr ⟨hd,hdK⟩) hdS
  · have hQR : totalWeight w Q ≤ totalWeight w R :=
      sum_le_sum_of_subset_of_nonneg subset_union_right (fun _ _ _ => by positivity)
    have hs : (totalWeight w K : ℝ)/(4*(f:ℝ)) ≤ (totalWeight w Q : ℝ) := by
      simpa only [totalWeight, NNReal.coe_sum] using hweight
    have hh := hs.trans (show (totalWeight w Q : ℝ) ≤ (totalWeight w R : ℝ) by exact_mod_cast hQR)
    have hfR : (0:ℝ) < 4*(f:ℝ) := by positivity
    simpa only [mul_comm] using (div_le_iff₀ hfR).mp hh

end LightEFTSpanners.NativeWeighted
