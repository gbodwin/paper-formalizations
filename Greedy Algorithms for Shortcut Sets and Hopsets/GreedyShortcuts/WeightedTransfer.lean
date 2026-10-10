import GreedyShortcuts.WeightedExpansion

/-! Transfer hopset improvements from a unique shortest-path perturbation back
to the original minimum-hop shortest paths, with faithful closure weights. -/
namespace GreedyShortcuts.WeightedPaths

open SimpleGraph DirectedPaths
open LinearDistancePreservers.ConsistentTiebreaking
open scoped NNReal
variable {V : Type*} [Fintype V] [DecidableEq V]

def CompatibleReweighting (G : V → V → Prop) (w w' : V → V → ℝ≥0) : Prop :=
  ∀ s t, Reachable G s t → ∃ p : DWalk s t, UniqueShortest G w' p ∧ MinHopShortest G w p

theorem CompatibleReweighting.minHopPath_shortest {G : V → V → Prop}
    {w w' : V → V → ℝ≥0} (h : CompatibleReweighting G w w')
    {s t : V} (hr : Reachable G s t) : Shortest G w (minHopPath G w' s t hr) := by
  obtain ⟨p, hp, hm⟩ := h s t hr
  rw [hp.2 _ (minHopPath_spec G w' s t hr).1]
  exact hm.1

theorem CompatibleReweighting.hop_eq {G : V → V → Prop}
    {w w' : V → V → ℝ≥0} (h : CompatibleReweighting G w w') (s t : V) :
    hopDistance G w' s t = hopDistance G w s t := by
  classical
  by_cases hr : Reachable G s t
  · obtain ⟨p, hp, hm⟩ := h s t hr
    rw [hopDistance_eq G w' hr, hp.2 _ (minHopPath_spec G w' s t hr).1]
    exact hm.length_eq_hopDistance
  · simp [hopDistance, hr]

/-- One expansion preserves both the perturbed and original augmented costs. -/
theorem CompatibleReweighting.lift {G : V → V → Prop} {w w' : V → V → ℝ≥0}
    (h : CompatibleReweighting G w w') (H : Finset (V × V)) (hH : H ⊆ candidates G)
    {s t : V} (q : DWalk s t) (hq : Allowed (augment G H) q) :
    ∃ r : DWalk s t, Allowed G r ∧
      cost w' r = cost (augmentWeight G w' H) q ∧
      cost w r = cost (augmentWeight G w H) q := by
  classical
  induction q with
  | nil => exact ⟨.nil, allowed_nil G _, by simp, by simp⟩
  | @cons s u t ha q ih =>
    have hall := (allowed_cons (augment G H) ha q).mp hq
    obtain ⟨r, hr, hc', hc⟩ := ih hall.2
    by_cases he : (s,u) ∈ H
    · have hs := ((mem_candidates G (s,u)).mp (hH he)).2
      let p := minHopPath G w' s u hs
      have hp' := (minHopPath_spec G w' s u hs).1
      have hp := h.minHopPath_shortest hs
      refine ⟨p.append r, (allowed_append G p r).mpr ⟨hp'.1,hr⟩, ?_, ?_⟩
      · rw [cost_append, cost_cons, hc', augmentWeight_of_mem G w' he]
        exact congrArg (fun x : ℝ => x + cost (augmentWeight G w' H) q) hp'.cost_eq_distance
      · rw [cost_append, cost_cons, hc, augmentWeight_of_mem G w he]
        exact congrArg (fun x : ℝ => x + cost (augmentWeight G w H) q) hp.cost_eq_distance
    · refine ⟨.cons ha r, (allowed_cons G ha r).mpr ⟨hall.1.resolve_right he,hr⟩, ?_, ?_⟩
      · simp only [cost_cons, hc', augmentWeight_of_not_mem G w' he]
      · simp only [cost_cons, hc, augmentWeight_of_not_mem G w he]

/-- Every augmented perturbed shortest walk is an original augmented shortest
walk. Its number of hops therefore bounds the original minimum hopdistance. -/
theorem CompatibleReweighting.augmented_shortest {G : V → V → Prop}
    {w w' : V → V → ℝ≥0} (h : CompatibleReweighting G w w')
    {H : Finset (V × V)} (hH : H ⊆ candidates G)
    {s t : V} {q : DWalk s t}
    (hq : Shortest (augment G H) (augmentWeight G w' H) q) :
    Shortest (augment G H) (augmentWeight G w H) q := by
  obtain ⟨r, hr, hc', hc⟩ := h.lift H hH q hq.1
  have hrs : Shortest G w' r := by
    apply (shortest_iff_cost_eq_distance hr).mpr
    rw [hc', hq.cost_eq_distance, distance_augment G w' H hH]
  obtain ⟨p, hp', hp⟩ := h s t ⟨r,hr⟩
  have he := hp'.2 r hrs
  apply (shortest_iff_cost_eq_distance hq.1).mpr
  rw [← hc, he, hp.1.cost_eq_distance, distance_augment G w H hH]

theorem CompatibleReweighting.hop_augment_le {G : V → V → Prop}
    {w w' : V → V → ℝ≥0} (h : CompatibleReweighting G w w')
    {H : Finset (V × V)} (hH : H ⊆ candidates G) (s t : V) :
    hopDistance (augment G H) (augmentWeight G w H) s t ≤
      hopDistance (augment G H) (augmentWeight G w' H) s t := by
  classical
  by_cases hr : Reachable (augment G H) s t
  · rw [hopDistance_eq (augment G H) (augmentWeight G w' H) hr]
    exact hopDistance_le_of_shortest (h.augmented_shortest hH
      (minHopPath_spec (augment G H) (augmentWeight G w' H) s t hr).1)
  · simp [hopDistance, hr]

end GreedyShortcuts.WeightedPaths
