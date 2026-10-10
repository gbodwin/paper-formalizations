import GreedyShortcuts.WeightedMonotonicity
import GreedyShortcuts.GraphGreedy

/-! Algorithm 1 for nonnegative weighted directed graphs. The potential uses
minimum-hop shortest paths and the state changes only explicitly inserted
closure edges. The main quantitative hopset-size theorem is still separate. -/
namespace GreedyShortcuts.WeightedGreedy

open Finset DirectedPaths GraphGreedy WeightedPaths
open scoped NNReal
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def potential (G : V → V → Prop) (w : V → V → ℝ≥0)
    (β : ℕ) (H : Finset (V × V)) : ℕ :=
  ∑ e ∈ candidates G,
    contribution β (hopDistance (augment G H) (augmentWeight G w H) e.1 e.2)

theorem potential_mono (G : V → V → Prop) (w : V → V → ℝ≥0) (β : ℕ)
    {H J : Finset (V × V)} (hH : H ⊆ candidates G) (hJ : J ⊆ candidates G) (hHJ : H ⊆ J) :
    potential G w β J ≤ potential G w β H := by
  apply Finset.sum_le_sum
  intro e he
  exact contribution_mono β (hopDistance_augment_mono G w hH hJ hHJ
    ((mem_candidates G e).mp he).2)

@[simp] theorem potential_eq_zero (G : V → V → Prop) (w : V → V → ℝ≥0)
    (β : ℕ) (H : Finset (V × V)) :
    potential G w β H = 0 ↔ ∀ e ∈ candidates G,
      hopDistance (augment G H) (augmentWeight G w H) e.1 e.2 ≤ β := by
  simp [potential, Finset.sum_eq_zero_iff]

theorem potential_progress (G : V → V → Prop) (w : V → V → ℝ≥0)
    (β : ℕ) (hβ : 1 ≤ β) (H : Finset (V × V)) (hH : H ⊆ candidates G)
    (hpos : 0 < potential G w β H) :
    ∃ e ∈ candidates G, potential G w β (insert e H) < potential G w β H := by
  have hex : ∃ e ∈ candidates G,
      0 < contribution β (hopDistance (augment G H) (augmentWeight G w H) e.1 e.2) := by
    by_contra hn
    push Not at hn
    have hz : potential G w β H = 0 :=
      Finset.sum_eq_zero (fun e he => Nat.eq_zero_of_le_zero (hn e he))
    omega
  obtain ⟨e, he, hd⟩ := hex
  refine ⟨e, he, ?_⟩
  apply Finset.sum_lt_sum
  · intro x hx
    exact contribution_mono β (hopDistance_augment_mono G w hH (Finset.insert_subset he hH)
      (Finset.subset_insert e H) ((mem_candidates G x).mp hx).2)
  · refine ⟨e, he, ?_⟩
    have hnew := (hopDistance_insert_edge G w hH he).trans hβ
    rw [(contribution_eq_zero β _).mpr hnew]
    exact hd

noncomputable def system (G : V → V → Prop) (w : V → V → ℝ≥0)
    (β : ℕ) (hβ : 1 ≤ β) : FiniteGreedy.System (V × V) where
  candidates := candidates G
  potential := potential G w β
  progress := fun H hH hpos => potential_progress G w β hβ H hH hpos

noncomputable def output (G : V → V → Prop) (w : V → V → ℝ≥0)
    (β : ℕ) (hβ : 1 ≤ β) : Finset (V × V) :=
  ((system G w β hβ).run (candidates G).card).1

theorem output_subset (G : V → V → Prop) (w : V → V → ℝ≥0) (β : ℕ) (hβ : 1 ≤ β) :
    output G w β hβ ⊆ candidates G :=
  ((system G w β hβ).run (candidates G).card).2

theorem output_zero (G : V → V → Prop) (w : V → V → ℝ≥0) (β : ℕ) (hβ : 1 ≤ β) :
    potential G w β (output G w β hβ) = 0 := (system G w β hβ).run_terminates

theorem output_distance (G : V → V → Prop) (w : V → V → ℝ≥0)
    (β : ℕ) (hβ : 1 ≤ β) (s t : V) :
    distance (augment G (output G w β hβ)) (augmentWeight G w (output G w β hβ)) s t =
      distance G w s t := distance_augment G w _ (output_subset G w β hβ) s t

theorem output_reachable_iff (G : V → V → Prop) (w : V → V → ℝ≥0)
    (β : ℕ) (hβ : 1 ≤ β) (s t : V) :
    Reachable (augment G (output G w β hβ)) s t ↔ Reachable G s t :=
  reachable_augment_iff G _ (output_subset G w β hβ) s t

theorem output_hop_bound (G : V → V → Prop) (w : V → V → ℝ≥0)
    (β : ℕ) (hβ : 1 ≤ β) {s t : V} (h : Reachable G s t) :
    hopDistance (augment G (output G w β hβ)) (augmentWeight G w (output G w β hβ)) s t ≤ β := by
  by_cases heq : s = t
  · subst t
    simp
  · exact (potential_eq_zero G w β _).mp (output_zero G w β hβ) (s, t)
      ((mem_candidates G (s, t)).mpr ⟨heq, h⟩)

theorem output_card_le (G : V → V → Prop) (w : V → V → ℝ≥0) (β : ℕ) (hβ : 1 ≤ β) :
    (output G w β hβ).card ≤ (Fintype.card V) ^ 2 :=
  (Finset.card_le_card (output_subset G w β hβ)).trans (candidates_card_le G)

theorem potential_le_cube (G : V → V → Prop) (w : V → V → ℝ≥0)
    (β : ℕ) (H : Finset (V × V)) : potential G w β H ≤ (Fintype.card V) ^ 3 := by
  calc
    potential G w β H ≤ ∑ _e ∈ candidates G, Fintype.card V := by
      apply Finset.sum_le_sum
      intro e _
      exact (contribution_le β _).trans (hopDistance_le_card _ _ _ _)
    _ = (candidates G).card * Fintype.card V := by simp
    _ ≤ (Fintype.card V) ^ 2 * Fintype.card V := Nat.mul_le_mul_right _ (candidates_card_le G)
    _ = (Fintype.card V) ^ 3 := by ring

end GreedyShortcuts.WeightedGreedy
