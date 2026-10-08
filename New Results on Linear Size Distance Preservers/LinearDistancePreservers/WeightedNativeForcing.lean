import LinearDistancePreservers.WalkSequence
import LinearDistancePreservers.PreserverForcing

/-! Transfer native unique-shortest-path proofs to the list-based weighted
distance, and force all covered edges of every distance-preserving subgraph. -/
namespace LinearDistancePreservers.WeightedNativeForcing
open SimpleGraph WeightedDigraph ConsistentTiebreaking
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable
variable {V I : Type*} [Fintype V] [DecidableEq V] {G H : SimpleGraph V}

noncomputable def realCost (w : V → V → ℝ≥0) {s t : V} (p : G.Walk s t) : ℝ :=
  (p.darts.map fun d => (w d.fst d.snd : ℝ)).sum

theorem realCost_nonneg (w : V → V → ℝ≥0) {s t : V} (p : G.Walk s t) :
    0 ≤ realCost w p := by
  apply List.sum_nonneg
  intro z hz
  obtain ⟨d, _, rfl⟩ := List.mem_map.mp hz
  exact (w d.fst d.snd).coe_nonneg

/-- A native shortest-path proof computes the actual infimum distance. -/
theorem distance_eq_cost (w : V → V → ℝ≥0) {s t : V} (p : G.Walk s t)
    (hmin : ∀ q : G.Walk s t, realCost w p ≤ realCost w q) :
    distance G.Adj (fun u v => (w u v : ℝ≥0∞)) s t =
      cost (fun u v => (w u v : ℝ≥0∞)) p.support := by
  apply le_antisymm
  · exact distance_le_cost (support_isWalk (fun d _ => d.adj))
  · apply le_sInf
    rintro c ⟨l, hl, rfl⟩
    obtain ⟨q, rfl⟩ := native_of_list_walk hl
    rw [cost_support, cost_support]
    exact ENNReal.ofReal_le_ofReal (hmin q)

theorem forces_edges (w : V → V → ℝ≥0) {s t : V} (p : G.Walk s t)
    (hmin : ∀ q : G.Walk s t, realCost w p ≤ realCost w q)
    (hunique : ∀ q : G.Walk s t, realCost w q = realCost w p → q = p)
    (hsub : H ≤ G)
    (hpres : distance H.Adj (fun u v => (w u v : ℝ≥0∞)) s t =
      distance G.Adj (fun u v => (w u v : ℝ≥0∞)) s t) :
    ∀ e ∈ p.edges, e ∈ H.edgeSet := by
  have hp : IsWalk G.Adj s t p.support := support_isWalk (fun d _ => d.adj)
  have huniq : ∀ l, IsWalk G.Adj s t l →
      cost (fun u v => (w u v : ℝ≥0∞)) l =
        distance G.Adj (fun u v => (w u v : ℝ≥0∞)) s t → l = p.support := by
    intro l hl he
    obtain ⟨q, rfl⟩ := native_of_list_walk hl
    rw [distance_eq_cost w p hmin, cost_support, cost_support] at he
    have heq : realCost w q = realCost w p := by
      have := congrArg ENNReal.toReal he
      change (ENNReal.ofReal (realCost w q)).toReal =
        (ENNReal.ofReal (realCost w p)).toReal at this
      simpa only [ENNReal.toReal_ofReal (realCost_nonneg w q),
        ENNReal.toReal_ofReal (realCost_nonneg w p)] using this
    rw [hunique q heq]
  have hforce := forces_edges_of_unique_shortest w s t p.support hp huniq
    (fun _ _ h => hsub h) hpres
  intro e he
  rw [SimpleGraph.Walk.edges, List.mem_map] at he
  obtain ⟨d, hd, rfl⟩ := he
  apply hforce (d.fst,d.snd)
  rw [zip_support]
  exact List.mem_map.mpr ⟨d, hd, rfl⟩

theorem eq_of_covers (w : V → V → ℝ≥0) (s t : I → V)
    (p : ∀ i, G.Walk (s i) (t i))
    (hmin : ∀ i (q : G.Walk (s i) (t i)), realCost w (p i) ≤ realCost w q)
    (hunique : ∀ i (q : G.Walk (s i) (t i)), realCost w q = realCost w (p i) → q = p i)
    (hcover : ∀ e ∈ G.edgeSet, ∃ i, e ∈ (p i).edges)
    (hsub : H ≤ G)
    (hpres : ∀ i, distance H.Adj (fun u v => (w u v : ℝ≥0∞)) (s i) (t i) =
      distance G.Adj (fun u v => (w u v : ℝ≥0∞)) (s i) (t i)) : H = G := by
  apply le_antisymm hsub
  intro u v huv
  obtain ⟨i, hi⟩ := hcover s(u,v) huv
  exact forces_edges w (p i) (hmin i) (hunique i) hsub (hpres i) _ hi

end LinearDistancePreservers.WeightedNativeForcing
