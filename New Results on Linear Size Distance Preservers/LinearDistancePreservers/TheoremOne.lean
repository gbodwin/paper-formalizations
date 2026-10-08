import LinearDistancePreservers.NativeWalkBridge
import LinearDistancePreservers.PaperTheorem

/-! Theorem 1 for arbitrary finite directed graphs with finite nonnegative
weights. Tiebreaking, shortest-path attainment, and the routing/edge-union
correspondence are all constructed. Zero weights, self-loops, empty vertex
sets and unreachable demands are supported. -/
namespace LinearDistancePreservers
open WeightedDigraph ConsistentTiebreaking SimpleGraph
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem distance_eq_top_of_no_walk (G : V → V → Prop) (w : V → V → ℝ≥0∞)
    (s t : V) (h : ¬ ∃ l, IsWalk G s t l) : distance G w s t = ⊤ := by
  have hempty : {c | ∃ l, IsWalk G s t l ∧ c = cost w l} = (∅ : Set ℝ≥0∞) := by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨l, hl, _⟩
    exact h ⟨l, hl⟩
  rw [distance, hempty, sInf_empty]

/-- A concrete finite form of Theorem 1. There is no assumed shortest-path
selection, consistency property, or routing input. -/
theorem theorem_one {p : ℕ} (G : V → V → Prop) (w : V → V → ℝ≥0)
    (s t : Fin p → V) :
    ∃ H : Finset (V × V),
      (∀ u v, (u,v) ∈ H → G u v) ∧
      (∀ i, distance (fun u v => (u,v) ∈ H) (fun u v => (w u v : ℝ≥0∞)) (s i) (t i) =
        distance G (fun u v => (w u v : ℝ≥0∞)) (s i) (t i)) ∧
      H.card ≤ 3 * Fintype.card V + 24 * p * (Nat.nthRoot 3 (Fintype.card V))^2 := by
  classical
  cases isEmpty_or_nonempty V
  · exact ⟨∅, fun u => isEmptyElim u, fun i => isEmptyElim (s i), by simp⟩
  let reachable (i : Fin p) : Prop := ∃ l, IsWalk G (s i) (t i) l
  let target (i : Fin p) : V := if reachable i then t i else s i
  have hex (i : Fin p) : ∃ q : (⊤ : SimpleGraph V).Walk (s i) (target i), Allowed G q := by
    by_cases hr : reachable i
    · have ht : target i = t i := if_pos hr
      rw [ht]
      obtain ⟨l, hl⟩ := hr
      obtain ⟨q, hq, _⟩ := exists_native_walk_le G w hl
      exact ⟨q, hq⟩
    · have ht : target i = s i := if_neg hr
      rw [ht]
      have hnil : Allowed G (Walk.nil : (⊤ : SimpleGraph V).Walk (s i) (s i)) := by simp [Allowed]
      exact ⟨Walk.nil, hnil⟩
  choose q hq using fun i => ConsistentTiebreaking.exists_optimal G w (s i) (target i) (hex i)
  obtain ⟨H, hHG, hdist, hsize⟩ := theorem_one_of_consistent_selection
    G (fun u v => (w u v : ℝ≥0∞)) s target (fun i => (q i).support)
    (routing s target q hq) (fun i => support_isWalk (hq i).1)
    (fun i => (hq i).attains_distance) (routing_edges_iff s target q hq) Fintype.card_pos
  refine ⟨H, hHG, ?_, hsize⟩
  intro i
  by_cases hr : reachable i
  · simpa only [target, if_pos hr] using hdist i
  · apply le_antisymm _ (distance_mono _ hHG (s i) (t i))
    rw [distance_eq_top_of_no_walk G _ (s i) (t i) hr]
    exact le_top

end LinearDistancePreservers
