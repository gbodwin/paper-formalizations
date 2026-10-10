import GreedyShortcuts.UndirectedProgress
import GreedyShortcuts.UndirectedPotential
import GreedyShortcuts.FiniteHorizon

/-! An exact finite undirected nonnegative-weight version of the near-existential
hopset guarantee. The benchmark quantifies over all finite vertex types of at most
the input cardinality, and every relation and weighting on each type. All budgets and exceptional small cases are explicit.
Both input and output budgets count unordered edges once; broader weight domains are not asserted here. -/
namespace GreedyShortcuts.UndirectedBenchmark

open Finset DirectedPaths WeightedPaths Undirected
open WeightedProgress (augment_empty_eq)
open scoped NNReal
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

noncomputable def edges (G : V → V → Prop) : Finset (Sym2 V) :=
  forget (WeightedBenchmark.edges G)

@[simp] theorem edges_augment (G : V → V → Prop) (H : Finset (Sym2 V)) :
    edges (augment G (arcs H)) = edges G ∪ H := by
  unfold edges
  rw [WeightedBenchmark.edges_augment]
  change forget (WeightedBenchmark.edges G ∪ arcs H) = _
  simp only [forget, Finset.image_union]
  rw [show (arcs H).image (fun e => s(e.1,e.2)) = H from forget_arcs H]

theorem edges_augment_card (G : V → V → Prop) (H : Finset (Sym2 V)) :
    (edges (augment G (arcs H))).card ≤ (edges G).card + H.card := by
  rw [edges_augment]
  exact Finset.card_union_le _ _

/-- Universal comparison property, with at most m unordered input edges and h
inserted closure edges. All finite vertex types of at most the input cardinality are quantified. -/
def UniversalBound (V : Type u) [Fintype V] [DecidableEq V] (m h B : ℕ) : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W], Fintype.card W ≤ Fintype.card V →
  ∀ (G : W → W → Prop), Symmetric G →
  ∀ (w : W → W → ℝ≥0), (∀ s t, w s t = w t s) → (edges G).card ≤ m →
    ∃ J : Finset (Sym2 W), J ⊆ candidates G ∧ J.card ≤ h ∧
      ∀ s t, Reachable G s t → hopDistance (augment G (arcs J)) (augmentWeight G w (arcs J)) s t ≤ B

theorem universal_card (m h : ℕ) : UniversalBound V m h (Fintype.card V) := by
  intro W _ _ hW G hG w hw hsize
  refine ⟨∅, Finset.empty_subset _, by simp, ?_⟩
  intro s t hr
  simpa only [arcs_empty, augment_empty_eq, augmentWeight_empty] using (hopDistance_le_card G w s t).trans hW

/-- Least universal hopbound. Existence is proved, not postulated. -/
noncomputable def exopt (V : Type u) [Fintype V] [DecidableEq V] (m h : ℕ) : ℕ := by
  classical
  exact Nat.find (show ∃ B, UniversalBound V m h B from ⟨Fintype.card V, universal_card m h⟩)

theorem exopt_spec (m h : ℕ) : UniversalBound V m h (exopt V m h) := by
  classical
  exact Nat.find_spec _

theorem exopt_le {m h B : ℕ} (hb : UniversalBound V m h B) : exopt V m h ≤ B := by
  classical
  exact Nat.find_min' _ hb

/-- The full graph-specific progress and stopping argument with exact finite
parameters. In particular, progress is used only while fewer than m edges have
been inserted, so every comparison graph has at most 2m edges. -/
theorem output_card_of_universal_bound (G : V → V → Prop) (w : V → V → ℝ≥0)
    (hG : Symmetric G) (hw : ∀ s t, w s t = w t s)
    (m h B β : ℕ) (hsize : (edges G).card ≤ m) (hβ : 1 ≤ β) (hB : 2 * B ≤ β)
    (hcompare : UniversalBound V (2 * m) h B)
    (hbudget : (Nat.log 2 ((Fintype.card V)^3) + 1) * (4*h) ≤ m) :
    (output G w hG β hβ).card ≤ m := by
  have hcurrent : ∀ H : Finset (Sym2 V), H.card ≤ m → ∀ w' : V → V → ℝ≥0, (∀ s t, w' s t = w' t s) →
      ∃ J : Finset (Sym2 V), J ⊆ candidates (augment G (arcs H)) ∧ J.card ≤ h ∧
        ∀ s t, Reachable (augment G (arcs H)) s t →
          hopDistance (augment (augment G (arcs H)) (arcs J)) (augmentWeight (augment G (arcs H)) w' (arcs J)) s t ≤ B := by
    intro H hc w' hw'
    apply hcompare V le_rfl (augment G (arcs H)) (augment_symmetric G hG H) w' hw'
    have he := edges_augment_card G H
    omega
  by_cases hh : h = 0
  · have hz : potential G w β ∅ = 0 := by
      by_contra hne
      obtain ⟨e, he, hp⟩ := state_progress G w hG hw ∅ (Finset.empty_subset _) h B β hB
        (hcurrent ∅ (by simp)) (Nat.pos_of_ne_zero hne)
      have hz' : potential G w β ∅ = 0 := by
        simpa only [hh, Nat.mul_zero, Nat.zero_mul, Nat.le_zero] using hp
      exact hne hz'
    have hc := (system G w hG β hβ).final_card_of_zero_at 0 (by simpa [system] using hz)
    exact hc.trans (Nat.zero_le m)
  · apply FiniteHorizon.output_card_before (system G w hG β hβ) (4*h)
      (Nat.log 2 ((Fintype.card V)^3) + 1) m (by omega) hbudget
    · intro S hS hpos
      exact state_progress G w hG hw S.1 S.2 h B β hB (hcurrent S.1 hS.le) hpos
    · exact (potential_le_cube G w β ∅).trans_lt (Nat.lt_pow_succ_log_self (by decide) _)

/-- Integer comparison-edge budget corresponding to the paper's sufficiently
small constant times m/log n, without undefined logarithms at n=0 or n=1. -/
def comparisonBudget (n m : ℕ) : ℕ := m / (4 * (Nat.log 2 (n^3) + 1))

theorem comparisonBudget_fits (n m : ℕ) :
    (Nat.log 2 (n^3) + 1) * (4 * comparisonBudget n m) ≤ m := by
  have h := Nat.div_mul_le_self m (4 * (Nat.log 2 (n^3) + 1))
  simpa [comparisonBudget, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

/-- Undirected nonnegative-weight near-existential guarantee for the actual
Algorithm 1 output, with the least universal benchmark and rounded budgets. -/
theorem undirected_near_existential (G : V → V → Prop) (w : V → V → ℝ≥0)
    (hG : Symmetric G) (hw : ∀ s t, w s t = w t s)
    (m : ℕ) (hsize : (edges G).card ≤ m) :
    let h := comparisonBudget (Fintype.card V) m
    let β := max 1 (2 * exopt V (2*m) h)
    (output G w hG β (Nat.le_max_left _ _)).card ≤ m ∧
      (∀ s t, distance (augment G (arcs (output G w hG β (Nat.le_max_left _ _))))
        (augmentWeight G w (arcs (output G w hG β (Nat.le_max_left _ _)))) s t = distance G w s t) ∧
      ∀ s t, Reachable G s t →
        hopDistance (augment G (arcs (output G w hG β (Nat.le_max_left _ _))))
          (augmentWeight G w (arcs (output G w hG β (Nat.le_max_left _ _)))) s t ≤ β := by
  dsimp only
  refine ⟨?_, output_distance G w hG _ _, fun s t hr => output_hop_bound G w hG _ _ hr⟩
  exact output_card_of_universal_bound G w hG hw m _ _ _ hsize (Nat.le_max_left _ _)
    (Nat.le_max_right _ _) (exopt_spec _ _) (comparisonBudget_fits _ _)

end GreedyShortcuts.UndirectedBenchmark
