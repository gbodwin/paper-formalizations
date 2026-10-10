import GreedyShortcuts.UndirectedArcs

/-! Actual finite greedy insertion of unordered hopedges. Each choice inserts
both directed realizations, while its cardinality is charged once. -/
namespace GreedyShortcuts.Undirected

open Finset DirectedPaths WeightedPaths
open scoped NNReal
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def potential (G : V → V → Prop) (w : V → V → ℝ≥0)
    (β : ℕ) (H : Finset (Sym2 V)) : ℕ := WeightedGreedy.potential G w β (arcs H)

theorem insert_arc_subset (H : Finset (Sym2 V)) (d : V × V) :
    insert d (arcs H) ⊆ arcs (insert s(d.1,d.2) H) := by
  intro e he
  rcases Finset.mem_insert.mp he with rfl | he
  · exact (mem_arcs _ e.1 e.2).mpr (Finset.mem_insert_self _ _)
  · exact arcs_mono (Finset.subset_insert _ H) he

theorem potential_progress (G : V → V → Prop) (w : V → V → ℝ≥0)
    (hG : Symmetric G) (β : ℕ) (hβ : 1 ≤ β)
    (H : Finset (Sym2 V)) (hH : H ⊆ candidates G) (hpos : 0 < potential G w β H) :
    ∃ e ∈ candidates G, potential G w β (insert e H) < potential G w β H := by
  have ha := arcs_subset_candidates G hG hH
  obtain ⟨d,hd,hdrop⟩ := WeightedGreedy.potential_progress G w β hβ (arcs H) ha hpos
  have he : s(d.1,d.2) ∈ candidates G := Finset.mem_image.mpr ⟨d,hd,rfl⟩
  refine ⟨s(d.1,d.2),he,lt_of_le_of_lt ?_ hdrop⟩
  exact WeightedGreedy.potential_mono G w β (Finset.insert_subset hd ha)
    (arcs_subset_candidates G hG (Finset.insert_subset he hH)) (insert_arc_subset H d)

noncomputable def system (G : V → V → Prop) (w : V → V → ℝ≥0)
    (hG : Symmetric G) (β : ℕ) (hβ : 1 ≤ β) : FiniteGreedy.System (Sym2 V) where
  candidates := candidates G
  potential := potential G w β
  progress := fun H hH hpos => potential_progress G w hG β hβ H hH hpos

noncomputable def output (G : V → V → Prop) (w : V → V → ℝ≥0)
    (hG : Symmetric G) (β : ℕ) (hβ : 1 ≤ β) : Finset (Sym2 V) :=
  ((system G w hG β hβ).run (candidates G).card).1

theorem output_subset (G : V → V → Prop) (w : V → V → ℝ≥0)
    (hG : Symmetric G) (β : ℕ) (hβ : 1 ≤ β) : output G w hG β hβ ⊆ candidates G :=
  ((system G w hG β hβ).run (candidates G).card).2

theorem output_zero (G : V → V → Prop) (w : V → V → ℝ≥0)
    (hG : Symmetric G) (β : ℕ) (hβ : 1 ≤ β) : potential G w β (output G w hG β hβ) = 0 :=
  (system G w hG β hβ).run_terminates

theorem output_distance (G : V → V → Prop) (w : V → V → ℝ≥0)
    (hG : Symmetric G) (β : ℕ) (hβ : 1 ≤ β) (s t : V) :
    distance (augment G (arcs (output G w hG β hβ)))
      (augmentWeight G w (arcs (output G w hG β hβ))) s t = distance G w s t :=
  distance_augment G w _ (arcs_subset_candidates G hG (output_subset G w hG β hβ)) s t

theorem output_hop_bound (G : V → V → Prop) (w : V → V → ℝ≥0)
    (hG : Symmetric G) (β : ℕ) (hβ : 1 ≤ β) {s t : V} (hr : Reachable G s t) :
    hopDistance (augment G (arcs (output G w hG β hβ)))
      (augmentWeight G w (arcs (output G w hG β hβ))) s t ≤ β := by
  by_cases he : s = t
  · subst t
    simp
  · exact (WeightedGreedy.potential_eq_zero G w β _).mp (output_zero G w hG β hβ) (s,t)
      ((mem_candidates G (s,t)).mpr ⟨he,hr⟩)

theorem potential_le_cube (G : V → V → Prop) (w : V → V → ℝ≥0)
    (β : ℕ) (H : Finset (Sym2 V)) : potential G w β H ≤ (Fintype.card V)^3 :=
  WeightedGreedy.potential_le_cube G w β (arcs H)

end GreedyShortcuts.Undirected
