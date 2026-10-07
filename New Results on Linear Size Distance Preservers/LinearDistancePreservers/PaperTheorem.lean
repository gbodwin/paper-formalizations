import LinearDistancePreservers.Batching
import LinearDistancePreservers.PathUnion

/-!
# Theorem 1 from an explicit consistent shortest-path selection

The input `R` supplies the consistency data of Lemma 2, `hvalid` and
`hshortest` supply actual shortest walks, and `hedges` identifies their union
with the routing edges. These are genuine remaining hypotheses. In
particular this theorem is not advertised as a proof of the existence of
consistent shortest-path tiebreaking in every weighted digraph.
-/
namespace LinearDistancePreservers
open scoped ENNReal
open WeightedDigraph
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Actual subgraph and exact distance preservation, together with the
integer cube-root form of Theorem 1's size bound, conditional on the
explicitly supplied consistent shortest-path selection. -/
theorem theorem_one_of_consistent_selection {p : ℕ}
    (G : V → V → Prop) (w : V → V → ℝ≥0∞) (s t : Fin p → V)
    (paths : Fin p → List V) (R : Routing (Fin p) V)
    (hvalid : ∀ i, IsWalk G (s i) (t i) (paths i))
    (hshortest : ∀ i, cost w (paths i) = distance G w (s i) (t i))
    (hedges : ∀ u v, PathUnion paths u v ↔ (v,u) ∈ R.edges)
    (hn : 0 < Fintype.card V) :
    ∃ H : Finset (V × V),
      (∀ u v, (u,v) ∈ H → G u v) ∧
      (∀ i, distance (fun u v => (u,v) ∈ H) w (s i) (t i) = distance G w (s i) (t i)) ∧
      H.card ≤ 3 * Fintype.card V + 24 * p * (Nat.nthRoot 3 (Fintype.card V))^2 := by
  classical
  let H := R.edges.image Prod.swap
  have hH (u v : V) : (u,v) ∈ H ↔ PathUnion paths u v := by
    rw [hedges]
    simp [H,Prod.swap,Finset.mem_image,Prod.ext_iff,and_comm]
  refine ⟨H,?_,?_,?_⟩
  · intro u v he
    exact path_union_subgraph paths s t hvalid u v ((hH u v).mp he)
  · intro i
    have hrel : (fun u v => (u,v) ∈ H) = PathUnion paths := by
      funext u v
      exact propext (hH u v)
    rw [hrel]
    exact path_union_preserves w paths s t hvalid hshortest i
  · exact Finset.card_image_le.trans (R.integer_theorem_one hn)

end LinearDistancePreservers
