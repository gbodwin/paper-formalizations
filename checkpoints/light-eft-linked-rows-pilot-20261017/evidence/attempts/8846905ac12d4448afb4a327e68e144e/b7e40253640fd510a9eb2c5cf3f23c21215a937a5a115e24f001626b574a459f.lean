import LightEFTSpanners.NativeSeedBudget
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

namespace LightEFTSpanners.NativeWeighted
open Finset SimpleGraph
open scoped NNReal
variable {V E I : Type*}
attribute [local instance] Classical.propDecidable

/-- Assign a candidate ID to every forest avoiding its explicit blocker set. -/
noncomputable def hostCandidates (U : Finset E) (T : I → Finset E)
    (block : E → Finset E) (i : I) : Finset E := U.filter fun e => Disjoint (T i) (block e)

theorem candidate_multiplicity [Fintype I] (U : Finset E) (T : I → Finset E)
    (block : E → Finset E) (f h : ℕ)
    (hcount : 2*f+h ≤ Fintype.card I) (hcap : ∀ e ∈ U, (block e).card ≤ f)
    (hcong : ∀ e, (univ.filter fun i => e ∈ T i).card ≤ 2) {e : E} (he : e ∈ U) :
    h ≤ (HostCounting.hosts univ (hostCandidates U T block) e).card := by
  classical
  have heq : HostCounting.hosts univ (hostCandidates U T block) e =
      univ.filter fun i => Disjoint (T i) (block e) := by
    ext i
    simp [HostCounting.hosts, hostCandidates, he]
  rw [heq]
  exact HostCounting.two_congestion_hosts univ T (block e) f h (by simpa using hcount)
    (hcap e he) (fun d _ => hcong d)

/-- The assignment gives actual weighted multiplicity on original IDs. -/
theorem candidate_weight_multiplicity [Fintype I] (w : E → ℝ≥0)
    (U : Finset E) (T : I → Finset E) (block : E → Finset E) (f h : ℕ)
    (hcount : 2*f+h ≤ Fintype.card I) (hcap : ∀ e ∈ U, (block e).card ≤ f)
    (hcong : ∀ e, (univ.filter fun i => e ∈ T i).card ≤ 2) :
    (h : ℝ) * (totalWeight w U : ℝ) ≤
      ∑ i, (totalWeight w (hostCandidates U T block i) : ℝ) := by
  classical
  simp only [totalWeight, NNReal.coe_sum]
  rw [HostCounting.weighted_incidence univ U (hostCandidates U T block)
    (fun e => (w e : ℝ)) (fun _ _ => filter_subset _ _), mul_sum]
  apply sum_le_sum
  intro e he
  exact mul_le_mul_of_nonneg_right
    (by exact_mod_cast candidate_multiplicity U T block f h hcount hcap hcong he)
    (NNReal.coe_nonneg _)

/-- Component bins retain the original ID and require both actual endpoints
inside the same component. Loops and parallel IDs are not identified. -/
noncomputable def componentCandidates (G : Graph V E) (T U : Finset E)
    (c : (G.restrict (T : Set E)).toSimpleGraph.ConnectedComponent) : Finset E :=
  U.filter fun e => ∃ u v : G.vertexSet, G.IsLink e u.val v.val ∧ u ∈ c.supp ∧ v ∈ c.supp

theorem mem_componentCandidates (G : Graph V E) (T U : Finset E)
    (c : (G.restrict (T : Set E)).toSimpleGraph.ConnectedComponent) (e : E) :
    e ∈ componentCandidates G T U c ↔ e ∈ U ∧
      ∃ u v : G.vertexSet, G.IsLink e u.val v.val ∧ u ∈ c.supp ∧ v ∈ c.supp := by
  exact mem_filter

theorem component_candidates_subset (G : Graph V E) (T U : Finset E)
    (c : (G.restrict (T : Set E)).toSimpleGraph.ConnectedComponent) :
    componentCandidates G T U c ⊆ U := filter_subset _ _

theorem component_candidate_unique (G : Graph V E) (T U : Finset E)
    {c d : (G.restrict (T : Set E)).toSimpleGraph.ConnectedComponent} {e : E}
    (hc : e ∈ componentCandidates G T U c) (hd : e ∈ componentCandidates G T U d) : c = d := by
  obtain ⟨_,u,v,hl,hu,_⟩ := mem_filter.mp hc
  obtain ⟨_,x,y,hl',hx,hy⟩ := mem_filter.mp hd
  have hud : u ∈ d.supp := by
    rcases hl.eq_and_eq_or_eq_and_eq hl' with ⟨hux,_⟩ | ⟨huy,_⟩
    · have h : u = x := Subtype.ext hux
      exact h ▸ hx
    · have h : u = y := Subtype.ext huy
      exact h ▸ hy
  exact ((ConnectedComponent.mem_supp_iff c u).mp hu).symm.trans
    ((ConnectedComponent.mem_supp_iff d u).mp hud)

/-- Every actual omitted candidate assigned to a forest lies in one component,
using the genuine forest walk supplied by the constructed seed budget. -/
theorem assigned_component_exists [Fintype V] [Fintype E]
    {G : Graph V E} {w : E → ℝ≥0} {H : Finset E} {q : ℕ}
    {T : Fin (q+1) → Finset E} (hb : SeedForestBudget G w H q T)
    (U : Finset E) (hU : U ⊆ inputEdges G \ H) (block : E → Finset E)
    (i : Fin (q+1)) {e : E} (he : e ∈ hostCandidates U T block i) :
    ∃ c, e ∈ componentCandidates G (T i) (hostCandidates U T block i) c := by
  classical
  have heU := (mem_filter.mp he).1
  obtain ⟨heG,heH⟩ := mem_sdiff.mp (hU heU)
  obtain ⟨u,v,hl⟩ := G.exists_isLink_of_mem_edgeSet (Set.mem_toFinset.mp heG)
  let a : G.vertexSet := ⟨u,hl.left_mem⟩
  let b : G.vertexSet := ⟨v,hl.right_mem⟩
  have hr := (walk_empty_iff_restrict G (T i) a b).mp (hb.paths i a b e hl heH)
  let F := (G.restrict (T i : Set E)).toSimpleGraph
  refine ⟨F.connectedComponentMk a, (mem_componentCandidates G _ _ _ _).mpr ⟨he,a,b,hl,?_,?_⟩⟩
  · rfl
  · exact ConnectedComponent.sound hr.symm

/-- Each host component really is a tree on its own vertex domain. This does
not assert that the disconnected forest spans one tree on all original V. -/
theorem host_component_tree {G : Graph V E} {w : E → ℝ≥0} {H : Finset E} {q : ℕ}
    {T : Fin (q+1) → Finset E} (hb : SeedForestBudget G w H q T)
    (i : Fin (q+1)) (c : (G.restrict (T i : Set E)).toSimpleGraph.ConnectedComponent) :
    c.toSimpleGraph.IsTree :=
  (MultigraphCuts.acyclic_of_all_edges_bridge _ (hb.forest i)).isTree_connectedComponent c

/-- Component candidate weights partition one forest's assigned weight exactly;
an ID is never charged twice within a host forest. -/
theorem sum_component_candidate_weights [Fintype V] [Fintype E]
    {G : Graph V E} {w : E → ℝ≥0} {H : Finset E} {q : ℕ}
    {T : Fin (q+1) → Finset E} (hb : SeedForestBudget G w H q T)
    (U : Finset E) (hU : U ⊆ inputEdges G \ H) (block : E → Finset E)
    (i : Fin (q+1)) :
    (∑ c, totalWeight w (componentCandidates G (T i) (hostCandidates U T block i) c)) =
      totalWeight w (hostCandidates U T block i) := by
  classical
  let A := hostCandidates U T block i
  let C := componentCandidates G (T i) A
  have hc (e) (he : e ∈ A) : (HostCounting.hosts univ C e).card = 1 := by
    obtain ⟨c,hc⟩ := assigned_component_exists hb U hU block i he
    apply card_eq_one.mpr
    refine ⟨c,?_⟩
    ext d
    simp only [HostCounting.hosts, mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · intro hd
      exact component_candidate_unique G (T i) A hd hc
    · intro heq
      subst d
      exact hc
  have hr : (∑ c, ∑ e ∈ C c, (w e : ℝ)) = ∑ e ∈ A, (w e : ℝ) := by
    rw [HostCounting.weighted_incidence univ A C (fun e => (w e : ℝ))
      (fun c _ => component_candidates_subset G (T i) A c)]
    apply sum_congr rfl
    intro e he
    rw [hc e he, Nat.cast_one, one_mul]
  unfold totalWeight
  exact_mod_cast hr

/-- Constructed native assignments satisfy the charging multiplicity and each
assigned ID has exactly one actual component host within each forest. -/
theorem native_assignment_properties [Fintype V] [Fintype E]
    {G : Graph V E} {w : E → ℝ≥0} {H : Finset E} {q : ℕ}
    {T : Fin (q+1) → Finset E} (hb : SeedForestBudget G w H q T)
    (U : Finset E) (hU : U ⊆ inputEdges G \ H) (block : E → Finset E)
    (f h : ℕ) (hcount : 2*f+h ≤ q+1) (hcap : ∀ e ∈ U, (block e).card ≤ f) :
    (∀ e ∈ U, h ≤ (HostCounting.hosts univ (hostCandidates U T block) e).card) ∧
    ((h : ℝ) * (totalWeight w U : ℝ) ≤ ∑ i, (totalWeight w (hostCandidates U T block i) : ℝ)) ∧
    ∀ i e, e ∈ hostCandidates U T block i →
      ∃! c : (G.restrict (T i : Set E)).toSimpleGraph.ConnectedComponent,
        e ∈ componentCandidates G (T i) (hostCandidates U T block i) c := by
  refine ⟨?_,?_,?_⟩
  · intro e he
    exact candidate_multiplicity U T block f h (by simpa using hcount) hcap hb.congestion he
  · exact candidate_weight_multiplicity w U T block f h (by simpa using hcount) hcap hb.congestion
  · intro i e he
    obtain ⟨c,hc⟩ := assigned_component_exists hb U hU block i he
    exact ⟨c,hc,fun d hd => component_candidate_unique G (T i) _ hd hc⟩

end LightEFTSpanners.NativeWeighted
