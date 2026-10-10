import GreedyShortcuts.DirectedPaths
import GreedyShortcuts.FiniteGreedy

/-!
Algorithm 1 for actual finite unweighted directed graphs. Its potential is the
sum of hop distances exceeding the target. Closure candidates are genuine
reachable ordered pairs. This file discharges the abstract algorithm's strict
progress interface and proves reachability, termination and hop correctness.
The sharper graph-specific progress bound of Theorem 1.4 is not assumed or
proved here; the unconditional size bound is the elementary quadratic one.
-/
namespace GreedyShortcuts.GraphGreedy

open DirectedPaths Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

def contribution (β d : ℕ) : ℕ := if β < d then d else 0

theorem contribution_mono (β : ℕ) : Monotone (contribution β) := by
  intro a b hab
  simp only [contribution]
  split_ifs <;> omega

@[simp] theorem contribution_eq_zero (β d : ℕ) : contribution β d = 0 ↔ d ≤ β := by
  simp only [contribution]
  split_ifs <;> omega

theorem contribution_le (β d : ℕ) : contribution β d ≤ d := by
  simp only [contribution]
  split_ifs <;> omega

noncomputable def potential (G : V → V → Prop) (β : ℕ) (H : Finset (V × V)) : ℕ :=
  ∑ e ∈ candidates G, contribution β (hopDist (augment G H) e.1 e.2)

theorem potential_antitone (G : V → V → Prop) (β : ℕ) : Antitone (potential G β) := by
  intro H J hHJ
  apply Finset.sum_le_sum
  intro e he
  exact contribution_mono β (hopDist_augment_antitone G hHJ
    ((mem_candidates G e).mp he).2)

@[simp] theorem potential_eq_zero (G : V → V → Prop) (β : ℕ) (H : Finset (V × V)) :
    potential G β H = 0 ↔
      ∀ e ∈ candidates G, hopDist (augment G H) e.1 e.2 ≤ β := by
  simp [potential, Finset.sum_eq_zero_iff]

/-- Every positive potential has a legal closure edge that removes at least
its own positive summand and increases none of the other summands. -/
theorem potential_progress (G : V → V → Prop) (β : ℕ) (hβ : 1 ≤ β)
    (H : Finset (V × V)) (hpos : 0 < potential G β H) :
    ∃ e ∈ candidates G, potential G β (insert e H) < potential G β H := by
  have hex : ∃ e ∈ candidates G,
      0 < contribution β (hopDist (augment G H) e.1 e.2) := by
    by_contra hn
    push Not at hn
    have hz : potential G β H = 0 :=
      Finset.sum_eq_zero (fun e he => Nat.eq_zero_of_le_zero (hn e he))
    omega
  obtain ⟨e, he, hd⟩ := hex
  refine ⟨e, he, ?_⟩
  apply Finset.sum_lt_sum
  · intro x hx
    exact contribution_mono β (hopDist_augment_antitone G (Finset.subset_insert e H)
      ((mem_candidates G x).mp hx).2)
  · refine ⟨e, he, ?_⟩
    have hnew : hopDist (augment G (insert e H)) e.1 e.2 ≤ β :=
      (hopDist_edge (G := augment G (insert e H)) (Or.inr (by simp))).trans hβ
    rw [(contribution_eq_zero β _).mpr hnew]
    exact hd

noncomputable def system (G : V → V → Prop) (β : ℕ) (hβ : 1 ≤ β) :
    FiniteGreedy.System (V × V) where
  candidates := candidates G
  potential := potential G β
  progress := fun H _ hpos => potential_progress G β hβ H hpos

/-- The final state of the actual maximum-potential-drop run. -/
noncomputable def output (G : V → V → Prop) (β : ℕ) (hβ : 1 ≤ β) : Finset (V × V) :=
  ((system G β hβ).run (candidates G).card).1

theorem output_subset (G : V → V → Prop) (β : ℕ) (hβ : 1 ≤ β) :
    output G β hβ ⊆ candidates G :=
  ((system G β hβ).run (candidates G).card).2

theorem output_zero (G : V → V → Prop) (β : ℕ) (hβ : 1 ≤ β) :
    potential G β (output G β hβ) = 0 :=
  (system G β hβ).run_terminates

theorem output_reachable_iff (G : V → V → Prop) (β : ℕ) (hβ : 1 ≤ β) (s t : V) :
    Reachable (augment G (output G β hβ)) s t ↔ Reachable G s t :=
  reachable_augment_iff G _ (output_subset G β hβ) s t

theorem output_hop_bound (G : V → V → Prop) (β : ℕ) (hβ : 1 ≤ β)
    {s t : V} (h : Reachable G s t) :
    hopDist (augment G (output G β hβ)) s t ≤ β := by
  by_cases heq : s = t
  · subst t
    simp
  · exact (potential_eq_zero G β _).mp (output_zero G β hβ) (s, t)
      ((mem_candidates G (s, t)).mpr ⟨heq, h⟩)

theorem candidates_card_le (G : V → V → Prop) :
    (candidates G).card ≤ (Fintype.card V) ^ 2 := by
  have hh := Finset.card_le_card (Finset.subset_univ (candidates G))
  simpa [Fintype.card_prod, pow_two] using hh

theorem output_card_le (G : V → V → Prop) (β : ℕ) (hβ : 1 ≤ β) :
    (output G β hβ).card ≤ (Fintype.card V) ^ 2 :=
  (Finset.card_le_card (output_subset G β hβ)).trans (candidates_card_le G)

theorem potential_le_cube (G : V → V → Prop) (β : ℕ) (H : Finset (V × V)) :
    potential G β H ≤ (Fintype.card V) ^ 3 := by
  calc
    potential G β H ≤ ∑ _e ∈ candidates G, Fintype.card V := by
      apply Finset.sum_le_sum
      intro e _
      exact (contribution_le β _).trans (hopDist_le_card _ _ _)
    _ = (candidates G).card * Fintype.card V := by simp
    _ ≤ (Fintype.card V) ^ 2 * Fintype.card V :=
      Nat.mul_le_mul_right _ (candidates_card_le G)
    _ = (Fintype.card V) ^ 3 := by ring

/-- Once the combinatorial relative-progress estimate is supplied, it applies
to this graph algorithm's actual output, with an explicit integer stopping time. -/
theorem output_card_of_relative_progress (G : V → V → Prop) (β : ℕ) (hβ : 1 ≤ β)
    (D k : ℕ) (hD : 0 < D)
    (hrelative : ∀ H ⊆ candidates G, 0 < potential G β H →
      ∃ e ∈ candidates G,
        potential G β H ≤ D * (potential G β H - potential G β (insert e H)))
    (hsmall : (Fintype.card V) ^ 3 < 2 ^ k) :
    (output G β hβ).card ≤ k * D := by
  apply (system G β hβ).final_card_of_relative_progress D k hD
  · intro S hpos
    exact hrelative S.1 S.2 hpos
  · exact (potential_le_cube G β ∅).trans_lt hsmall

end GreedyShortcuts.GraphGreedy
