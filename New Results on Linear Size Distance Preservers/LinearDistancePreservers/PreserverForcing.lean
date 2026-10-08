import LinearDistancePreservers.NativeWalkBridge
import Mathlib.Combinatorics.SimpleGraph.Metric

/-! The edge-forcing step used in Section 4, with attainment proved rather
than assumed. The weighted result uses the same list-walk infimum distance
as Theorem 1. The unweighted result uses mathlib's extended graph distance.
Both apply to arbitrary subgraphs preserving the designated distances. -/
namespace LinearDistancePreservers
open SimpleGraph
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

namespace WeightedDigraph
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- In a finite graph with finite nonnegative weights, every finite distance
is attained. Zero-weight edges and directed self-loops are allowed. -/
theorem exists_shortest_of_distance_ne_top (G : V → V → Prop)
    (w : V → V → ℝ≥0) (s t : V)
    (hfin : distance G (fun u v => (w u v : ℝ≥0∞)) s t ≠ ⊤) :
    ∃ p, IsWalk G s t p ∧
      cost (fun u v => (w u v : ℝ≥0∞)) p =
        distance G (fun u v => (w u v : ℝ≥0∞)) s t := by
  have hex : ∃ p, IsWalk G s t p := by
    by_contra hn
    apply hfin
    have hempty : {c | ∃ p, IsWalk G s t p ∧
        c = cost (fun u v => (w u v : ℝ≥0∞)) p} = ∅ := by
      ext c
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨p, hp, _⟩
      exact hn ⟨p, hp⟩
    simp [distance, hempty]
  obtain ⟨l, hl⟩ := hex
  obtain ⟨p, hp, _⟩ := ConsistentTiebreaking.exists_native_walk_le G w hl
  obtain ⟨q, hq⟩ := ConsistentTiebreaking.exists_optimal G w s t ⟨p, hp⟩
  exact ⟨q.support, ConsistentTiebreaking.support_isWalk hq.1, hq.attains_distance⟩

/-- A unique shortest walk forces its edges into every equal-distance
subgraph. No shortest walk in the subgraph is supplied as a hypothesis. -/
theorem forces_edges_of_unique_shortest {G H : V → V → Prop}
    (w : V → V → ℝ≥0) (s t : V) (p : List V)
    (hp : IsWalk G s t p)
    (hunique : ∀ q, IsWalk G s t q →
      cost (fun u v => (w u v : ℝ≥0∞)) q =
        distance G (fun u v => (w u v : ℝ≥0∞)) s t → q = p)
    (hsub : ∀ u v, H u v → G u v)
    (hpres : distance H (fun u v => (w u v : ℝ≥0∞)) s t =
      distance G (fun u v => (w u v : ℝ≥0∞)) s t) :
    ∀ e ∈ p.zip p.tail, H e.1 e.2 := by
  have hcost : cost (fun u v => (w u v : ℝ≥0∞)) p ≠ ⊤ := by
    unfold cost
    generalize p.zip p.tail = l
    induction l with
    | nil => simp
    | cons e l ih =>
      simpa only [List.map_cons, List.sum_cons, ENNReal.add_ne_top] using
        And.intro (ENNReal.coe_ne_top) ih
  have hfin : distance H (fun u v => (w u v : ℝ≥0∞)) s t ≠ ⊤ := by
    rw [hpres]
    exact ne_top_of_le_ne_top hcost (distance_le_cost hp)
  obtain ⟨q, hq, heq⟩ := exists_shortest_of_distance_ne_top H w s t hfin
  exact unique_shortest_forces_edges _ s t p q hsub hunique hq heq hpres

end WeightedDigraph

namespace UnweightedForcing
variable {V I : Type*} {G H : SimpleGraph V}

/-- The native unweighted counterpart, including disconnected subgraphs. -/
theorem forces_edges {s t : V} (p : G.Walk s t)
    (hunique : ∀ q : G.Walk s t, q.length ≤ p.length → q = p)
    (hsub : H ≤ G) (hpres : H.edist s t = G.edist s t) :
    ∀ e ∈ p.edges, e ∈ H.edgeSet := by
  have hfin : H.edist s t ≠ ⊤ := by
    rw [hpres]
    exact edist_ne_top_iff_reachable.mpr p.reachable
  obtain ⟨q, hq⟩ := exists_walk_of_edist_ne_top hfin
  have hlen : q.length ≤ p.length := by
    have : (q.length : ℕ∞) ≤ p.length := by
      rw [hq, hpres]
      exact G.edist_le p
    exact_mod_cast this
  have heq : q.map (Hom.ofLE hsub) = p :=
    hunique _ (by simpa using hlen)
  intro e he
  rw [← heq] at he
  have : e ∈ q.edges := by simpa using he
  exact q.edges_subset_edgeSet this

/-- If designated unique shortest paths cover the edges, preservation of
their endpoint distances forces the entire graph. Edge-disjointness is
needed for counting, but not for this forcing implication. -/
theorem eq_of_covers (s t : I → V) (p : ∀ i, G.Walk (s i) (t i))
    (hunique : ∀ i (q : G.Walk (s i) (t i)), q.length ≤ (p i).length → q = p i)
    (hcover : ∀ e ∈ G.edgeSet, ∃ i, e ∈ (p i).edges)
    (hsub : H ≤ G) (hpres : ∀ i, H.edist (s i) (t i) = G.edist (s i) (t i)) : H = G := by
  apply le_antisymm hsub
  intro u v huv
  obtain ⟨i, hi⟩ := hcover s(u,v) huv
  exact forces_edges (p i) (hunique i) hsub (hpres i) _ hi

end UnweightedForcing
end LinearDistancePreservers
