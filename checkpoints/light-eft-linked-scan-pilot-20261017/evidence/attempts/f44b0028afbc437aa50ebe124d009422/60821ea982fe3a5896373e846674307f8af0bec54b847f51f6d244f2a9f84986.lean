import LightEFTSpanners.NativeHeavyLightCounts

/-! Sampling only nonseed blockers while retaining disjointness from the full
actual blocker family. U is any actual nonseed candidate subfamily. -/
namespace LightEFTSpanners.NativeWeighted
open Finset SimpleGraph
open scoped NNReal
variable {V E : Type*}
attribute [local instance] Classical.propDecidable

/-- Seed blockers are excluded by the original host assignment; sampled IDs
avoid residual blockers. Thus every surviving candidate avoids full blockers
throughout the sampled host, including its component forest. -/
theorem exists_residual_sampled_component_host [Fintype V] [Fintype E]
    {G : Graph V E} {w : E → ℝ≥0} {H : Finset E} {q : ℕ}
    {T : Fin (q+1) → Finset E} (hb : SeedForestBudget G w H q T)
    (U : Finset E) (hU : U ⊆ inputEdges G \ H) (block : E → Finset E)
    (r : ℕ) (hr : 0 < r) (hcap : ∀ e ∈ U, (block e \ H).card ≤ r)
    (hself : ∀ e ∈ U, e ∉ block e) (i : Fin (q+1))
    (c : (G.restrict (T i : Set E)).toSimpleGraph.ConnectedComponent) :
    let K := componentCandidates G (T i) (hostCandidates U T block i) c
    ∃ (S R : Finset E), S ⊆ K ∧
      R = componentForest G (T i) c ∪ BlockerSampling.surviving K (fun e => block e \ H) S ∧
      R ⊆ inputEdges G ∧ componentForest G (T i) c ⊆ R ∧
      c.toSimpleGraph.IsTree ∧
      (∀ e ∈ R, ∃ u v : G.vertexSet, G.IsLink e u.val v.val ∧ u ∈ c.supp ∧ v ∈ c.supp) ∧
      (∀ e ∈ BlockerSampling.surviving K (fun e => block e \ H) S, Disjoint (block e) R) ∧
      (totalWeight w K : ℝ) ≤ 4*(r:ℝ)*(totalWeight w R : ℝ) := by
  classical
  dsimp only
  let A := hostCandidates U T block i
  let K := componentCandidates G (T i) A c
  let F := componentForest G (T i) c
  have hKA : K ⊆ A := component_candidates_subset G (T i) A c
  have hAU : A ⊆ U := filter_subset _ _
  have hKU : K ⊆ U := hKA.trans hAU
  obtain ⟨S,hSK,hweight⟩ := BlockerSampling.exists_heavy_surviving_sample K (fun e => block e \ H)
    (fun e => (w e : ℝ)) (fun _ _ => NNReal.coe_nonneg _) r hr
    (fun e he => hcap e (hKU he)) (fun e he => fun hd => hself e (hKU he) (mem_sdiff.mp hd).1)
  let Q := BlockerSampling.surviving K (fun e => block e \ H) S
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
      exact Finset.disjoint_left.mp hdis (mem_inter.mpr ⟨mem_sdiff.mpr ⟨hd,(mem_sdiff.mp (hU (hKU hdK))).2⟩,hdK⟩) hdS
  · have hQR : totalWeight w Q ≤ totalWeight w R :=
      sum_le_sum_of_subset_of_nonneg subset_union_right (fun _ _ _ => by positivity)
    have hs : (totalWeight w K : ℝ)/(4*(r:ℝ)) ≤ (totalWeight w Q : ℝ) := by
      simpa only [totalWeight, NNReal.coe_sum] using hweight
    have hh := hs.trans (show (totalWeight w Q : ℝ) ≤ (totalWeight w R : ℝ) by exact_mod_cast hQR)
    have hrR : (0:ℝ) < 4*(r:ℝ) := by positivity
    simpa only [mul_comm] using (div_le_iff₀ hrR).mp hh

end LightEFTSpanners.NativeWeighted
