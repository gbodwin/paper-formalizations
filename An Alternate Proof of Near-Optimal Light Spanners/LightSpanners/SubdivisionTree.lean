import LightSpanners.SubdivisionCycles
import LightSpanners.Weight

/-! The explicit one-edge subdivision preserves spanning trees and their
bottleneck optimality certificates. -/
namespace LightSpanners
open SimpleGraph
variable {V : Type*}

theorem subdivideEdge_mono {G H : SimpleGraph V} (h : G ≤ H) (u v : V) :
    subdivideEdge G u v ≤ subdivideEdge H u v := by
  intro x y hxy
  cases x <;> cases y
  · exact hxy
  · exact hxy
  · exact hxy
  · exact ⟨h hxy.1, hxy.2⟩

/-- Subdividing an actual forest edge cannot create a cycle. -/
theorem subdivideEdge_isAcyclic {G : SimpleGraph V} {u v : V}
    (huv : G.Adj u v) (hG : G.IsAcyclic) : (subdivideEdge G u v).IsAcyclic := by
  intro z p hp
  obtain ⟨a, q, hq, _⟩ := subdivision_cycle_contract huv (fun _ => 0)
    (α := 0) (β := 0) (by norm_num) p hp
  exact hG q hq

theorem subdivideEdge_isTree {G : SimpleGraph V} {u v : V}
    (huv : G.Adj u v) (hG : G.IsTree) : (subdivideEdge G u v).IsTree :=
  ⟨subdivideEdge_connected huv hG.connected, subdivideEdge_isAcyclic huv hG.isAcyclic⟩

/-- A bound on every traversed edge is retained when the selected edge is
replaced by two individually no-heavier edges. This is a bottleneck bound,
rather than a bound on total walk weight. -/
theorem exists_subdivision_bounded_lift {G : SimpleGraph V} {u v : V}
    (huv : G.Adj u v) (w : Sym2 V → ℝ) {α β L : ℝ}
    (hα : α ≤ w s(u,v)) (hβ : β ≤ w s(u,v))
    {x y : V} (p : G.Walk x y) (hp : ∀ e ∈ p.edges, w e ≤ L) :
    ∃ q : (subdivideEdge G u v).Walk (some x) (some y),
      ∀ e ∈ q.edges, subdivideWeight w u α β e ≤ L := by
  classical
  induction p with
  | nil => exact ⟨.nil, by simp⟩
  | @cons x z y hxz p ih =>
    obtain ⟨q, hq⟩ := ih (fun e he => hp e (by simp [he]))
    have hfirst : w s(x,z) ≤ L := hp _ (by simp)
    by_cases he : s(x,z) = s(u,v)
    · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · refine ⟨.cons (subdivision_adj_new_left G x z)
          (.cons (subdivision_adj_new_right G x z).symm q), ?_⟩
        intro e he
        simp only [Walk.edges_cons, List.mem_cons] at he
        rcases he with rfl | rfl | he
        · simpa only [subdivideWeight_new', ite_true] using hα.trans hfirst
        · simpa only [subdivideWeight_new,
            ite_eq_right (by simpa using huv.ne.symm)] using hβ.trans hfirst
        · exact hq e he
      · refine ⟨.cons (subdivision_adj_new_right G z x)
          (.cons (subdivision_adj_new_left G z x).symm q), ?_⟩
        have hfirst' : w s(z,x) ≤ L := by simpa only [Sym2.eq_swap] using hfirst
        intro e he
        simp only [Walk.edges_cons, List.mem_cons] at he
        rcases he with rfl | rfl | he
        · simpa only [subdivideWeight_new',
            ite_eq_right (by simpa using huv.ne.symm)] using hβ.trans hfirst'
        · simpa only [subdivideWeight_new, ite_true] using hα.trans hfirst'
        · exact hq e he
    · refine ⟨.cons (subdivision_adj_old hxz he) q, ?_⟩
      intro e he
      simp only [Walk.edges_cons, List.mem_cons] at he
      rcases he with rfl | he
      · exact hfirst
      · exact hq e he

/-- Subdivision of a tree edge preserves its bottleneck-path certificate when
the two new weights are nonnegative and sum to the original weight. -/
theorem HasBottleneckPaths.subdivideEdge {G T : SimpleGraph V} {u v : V}
    {w : Sym2 V → ℝ} (hopt : HasBottleneckPaths G T w) (huv : T.Adj u v)
    {α β : ℝ} (hsum : α + β = w s(u,v)) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    HasBottleneckPaths (subdivideEdge G u v) (subdivideEdge T u v)
      (subdivideWeight w u α β) := by
  intro x y hxy
  cases x with
  | none =>
    cases y with
    | none => exact hxy.elim
    | some y =>
      have ht : (LightSpanners.subdivideEdge T u v).Adj none (some y) := hxy
      exact ⟨.cons ht .nil, by simp⟩
  | some x =>
    cases y with
    | none =>
      have ht : (LightSpanners.subdivideEdge T u v).Adj (some x) none := hxy
      exact ⟨.cons ht .nil, by simp⟩
    | some y =>
      obtain ⟨p, hp⟩ := hopt x y hxy.1
      exact exists_subdivision_bounded_lift huv w (by linarith) (by linarith) p hp

variable [DecidableEq V] [Fintype V]
attribute [local instance] Classical.propDecidable

/-- A bottleneck-certified spanning tree stays a minimum spanning tree after
subdivision of one of its edges. The certificate is constructive in walks. -/
theorem subdivision_isMinimumSpanningTree {G T : SimpleGraph V} {u v : V}
    {w : Sym2 V → ℝ} (hT : T.IsTree) (hTG : T ≤ G)
    (hopt : HasBottleneckPaths G T w) (huv : T.Adj u v)
    {α β : ℝ} (hsum : α + β = w s(u,v)) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    IsMinimumSpanningTree (subdivideEdge G u v) (subdivideEdge T u v)
      (subdivideWeight w u α β) :=
  minimumSpanningTree_of_bottleneck (subdivideEdge_isTree huv hT)
    (subdivideEdge_mono hTG u v) (hopt.subdivideEdge huv hsum hα hβ)

/-- The exact edge set of the subdivision: two new edges and all old edges
except for the subdivided edge. -/
theorem subdivision_edgeFinset (G : SimpleGraph V) (u v : V) :
    (subdivideEdge G u v).edgeFinset =
      insert s(some u, none) (insert s(some v, none)
        ((G.edgeFinset.erase s(u,v)).image (Sym2.map some))) := by
  classical
  ext e
  induction e using Sym2.inductionOn with
  | hf x y =>
    cases x <;> cases y <;>
      simp only [mem_edgeFinset, Finset.mem_insert, Finset.mem_image, Finset.mem_erase,
        Sym2.exists, Sym2.map_mk, Sym2.eq_iff, Option.some.injEq]
    all_goals simp [subdivideEdge]
    aesop (add safe forward SimpleGraph.Adj.symm)

/-- The total weight of all graph edges is exactly preserved by one-edge
subdivision. No sign restriction on the replacement weights is needed. -/
theorem totalWeight_subdivideEdge {G : SimpleGraph V} {u v : V}
    (huv : G.Adj u v) (w : Sym2 V → ℝ) {α β : ℝ}
    (hsum : α + β = w s(u,v)) :
    totalWeight (subdivideEdge G u v) (subdivideWeight w u α β) = totalWeight G w := by
  classical
  have hnew (x : V) : s(some x, none) ∉
      (G.edgeFinset.erase s(u,v)).image (Sym2.map some) := by
    simp [Finset.mem_image, Sym2.exists]
  have hneq : s(some u, none) ≠ s(some v, none) := by
    simpa [Sym2.eq_iff] using huv.ne
  have hmap (e : Sym2 V) :
      subdivideWeight w u α β (Sym2.map some e) = w e := by
    induction e using Sym2.inductionOn with | hf x y => rfl
  unfold totalWeight
  rw [subdivision_edgeFinset, Finset.sum_insert (by simp only [Finset.mem_insert]; exact not_or.mpr ⟨hneq, hnew u⟩),
    Finset.sum_insert (hnew v), Finset.sum_image]
  · simp only [hmap, subdivideWeight_new', ite_true,
      ite_eq_right (by simpa using huv.ne.symm)]
    rw [Finset.sum_erase_eq_sub (by simpa using (mem_edgeSet G).mpr huv)]
    linarith
  · intro a _ b _ hab
    exact Sym2.map.injective (Option.some_injective V) hab

/-- Subdivision of a spanning-tree edge preserves graph/tree weight ratio. -/
theorem lightness_subdivideEdge {G T : SimpleGraph V} {u v : V}
    (hTG : T ≤ G) (huv : T.Adj u v) (w : Sym2 V → ℝ) {α β : ℝ}
    (hsum : α + β = w s(u,v)) :
    lightness (subdivideEdge G u v) (subdivideEdge T u v) (subdivideWeight w u α β) =
      lightness G T w := by
  rw [lightness, totalWeight_subdivideEdge (hTG huv) w hsum,
    totalWeight_subdivideEdge huv w hsum, lightness]

end LightSpanners
