import GreedyShortcuts.WeightedHopDistance

/-! Insertion preserves shortest-path costs while decreasing minimum-hop
shortest-path lengths, including when it improves a parallel original edge. -/
namespace GreedyShortcuts.WeightedPaths

open SimpleGraph DirectedPaths
open LinearDistancePreservers.ConsistentTiebreaking
open scoped NNReal
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem augmentWeight_mono {G : V → V → Prop} (w : V → V → ℝ≥0)
    {H J : Finset (V × V)} (hHJ : H ⊆ J) {s t : V} (he : augment G H s t) :
    augmentWeight G w J s t ≤ augmentWeight G w H s t := by
  classical
  by_cases hH : (s, t) ∈ H
  · simp [augmentWeight, hH, hHJ hH]
  · have hG := he.resolve_right hH
    rw [augmentWeight_of_not_mem G w hH]
    exact augmentWeight_le_on_edge w J hG

theorem cost_augment_mono {G : V → V → Prop} (w : V → V → ℝ≥0)
    {H J : Finset (V × V)} (hHJ : H ⊆ J) {s t : V} (p : DWalk s t)
    (hp : Allowed (augment G H) p) :
    cost (augmentWeight G w J) p ≤ cost (augmentWeight G w H) p := by
  induction p with
  | nil => simp
  | cons h p ih =>
    have ha := (allowed_cons (augment G H) h p).mp hp
    simp only [cost_cons]
    exact add_le_add (by exact_mod_cast augmentWeight_mono w hHJ ha.1) (ih ha.2)

theorem Shortest.augment_mono {G : V → V → Prop} {w : V → V → ℝ≥0}
    {H J : Finset (V × V)} (hH : H ⊆ candidates G) (hJ : J ⊆ candidates G)
    (hHJ : H ⊆ J) {s t : V} {p : DWalk s t}
    (hp : Shortest (augment G H) (augmentWeight G w H) p) :
    Shortest (augment G J) (augmentWeight G w J) p := by
  refine ⟨allowed_mono (fun _ _ he => he.elim Or.inl (fun h => Or.inr (hHJ h))) hp.1, ?_⟩
  intro q hq
  calc
    cost (augmentWeight G w J) p ≤ cost (augmentWeight G w H) p :=
      cost_augment_mono w hHJ p hp.1
    _ = (distance (augment G H) (augmentWeight G w H) s t : ℝ) := hp.cost_eq_distance
    _ = (distance G w s t : ℝ) := by rw [distance_augment G w H hH]
    _ = (distance (augment G J) (augmentWeight G w J) s t : ℝ) := by
      rw [distance_augment G w J hJ]
    _ ≤ cost (augmentWeight G w J) q := distance_le_cost _ _ q hq

theorem hopDistance_augment_mono (G : V → V → Prop) (w : V → V → ℝ≥0)
    {H J : Finset (V × V)} (hH : H ⊆ candidates G) (hJ : J ⊆ candidates G)
    (hHJ : H ⊆ J) {s t : V} (hr : Reachable G s t) :
    hopDistance (augment G J) (augmentWeight G w J) s t ≤
      hopDistance (augment G H) (augmentWeight G w H) s t := by
  have ha := reachable_augment G H hr
  rw [hopDistance_eq _ _ ha]
  exact hopDistance_le_of_shortest
    ((minHopPath_spec (augment G H) (augmentWeight G w H) s t ha).1.augment_mono hH hJ hHJ)

theorem hopDistance_insert_edge (G : V → V → Prop) (w : V → V → ℝ≥0)
    {H : Finset (V × V)} (hH : H ⊆ candidates G) {e : V × V} (he : e ∈ candidates G) :
    hopDistance (augment G (insert e H)) (augmentWeight G w (insert e H)) e.1 e.2 ≤ 1 := by
  have hne := ((mem_candidates G e).mp he).1
  have hJ : insert e H ⊆ candidates G := Finset.insert_subset he hH
  let p : DWalk e.1 e.2 := .cons (by simpa using hne) .nil
  have hp : Allowed (augment G (insert e H)) p := by simp [p, augment]
  have hs : Shortest (augment G (insert e H)) (augmentWeight G w (insert e H)) p := by
    apply (shortest_iff_cost_eq_distance hp).mpr
    simp [p, augmentWeight, distance_augment G w (insert e H) hJ]
  simpa [p] using hopDistance_le_of_shortest hs

theorem hopDistance_le_card (G : V → V → Prop) (w : V → V → ℝ≥0) (s t : V) :
    hopDistance G w s t ≤ Fintype.card V := by
  classical
  by_cases h : Reachable G s t
  · exact (hopDistance_lt_card G w h).le
  · simp [hopDistance, h]

end GreedyShortcuts.WeightedPaths
