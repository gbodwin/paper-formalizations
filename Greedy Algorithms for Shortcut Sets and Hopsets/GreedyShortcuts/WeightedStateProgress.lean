import GreedyShortcuts.WeightedProgress
import GreedyShortcuts.WeightedTransfer

/-! The unique-shortest comparison bound transfers to the actual current
weighted greedy state. Its only remaining premise is a comparison hopset for
the perturbed current graph. -/
namespace GreedyShortcuts.WeightedStateProgress

open Finset DirectedPaths WeightedPaths WeightedGreedy
open WeightedProgress (augment_empty_eq)
open scoped NNReal
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem candidates_augment (G : V → V → Prop) (H : Finset (V × V))
    (hH : H ⊆ candidates G) : candidates (augment G H) = candidates G := by
  ext e
  simp only [mem_candidates, reachable_augment_iff G H hH]

theorem potential_current (G : V → V → Prop) (w : V → V → ℝ≥0)
    (β : ℕ) (H : Finset (V × V)) (hH : H ⊆ candidates G) :
    potential (augment G H) (augmentWeight G w H) β ∅ = potential G w β H := by
  simp only [potential, candidates_augment G H hH, augment_empty_eq, augmentWeight_empty]

theorem potential_current_insert (G : V → V → Prop) (w : V → V → ℝ≥0)
    (β : ℕ) (H : Finset (V × V)) (hH : H ⊆ candidates G) (e : V × V) :
    potential (augment G H) (augmentWeight G w H) β {e} = potential G w β (insert e H) := by
  simp only [potential, candidates_augment G H hH, augment_insert_eq, augmentWeight_insert_eq G w H hH]

theorem potential_reweight_le {G : V → V → Prop} {w w' : V → V → ℝ≥0}
    (h : CompatibleReweighting G w w') (β : ℕ) {H : Finset (V × V)} (hH : H ⊆ candidates G) :
    potential G w β H ≤ potential G w' β H := by
  apply Finset.sum_le_sum
  intro d hd
  exact GraphGreedy.contribution_mono β (h.hop_augment_le hH d.1 d.2)

theorem potential_reweight_empty {G : V → V → Prop} {w w' : V → V → ℝ≥0}
    (h : CompatibleReweighting G w w') (β : ℕ) : potential G w' β ∅ = potential G w β ∅ := by
  simp only [potential, augment_empty_eq, augmentWeight_empty, h.hop_eq]

/-- Comparison progress is valid in the original weights, even though the
comparison hopset was chosen for the perturbed graph. -/
theorem transfer_comparison (G : V → V → Prop) (w w' : V → V → ℝ≥0)
    (hc : CompatibleReweighting G w w')
    (J : Finset (V × V)) (hJ : J ⊆ candidates G) (B β : ℕ) (hB : 2 * B ≤ β)
    (hbound : ∀ s t, Reachable G s t → hopDistance (augment G J) (augmentWeight G w' J) s t ≤ B)
    (hpos : 0 < potential G w β ∅) :
    ∃ e ∈ J, potential G w β ∅ ≤ (2 * J.card) * (potential G w β ∅ - potential G w β {e}) := by
  have hunique : ∀ s t, Reachable G s t → ∃ p : DWalk s t, UniqueShortest G w' p := by
    intro s t hr
    obtain ⟨p,hp,hm⟩ := hc s t hr
    exact ⟨p,hp⟩
  obtain ⟨e, he, hg⟩ := WeightedProgress.comparison_progress G w' hunique J hJ B β hB hbound
    (by simpa only [potential_reweight_empty hc β] using hpos)
  rw [potential_reweight_empty hc β] at hg
  refine ⟨e, he, hg.trans ?_⟩
  apply Nat.mul_le_mul_left
  exact Nat.sub_le_sub_left (potential_reweight_le hc β (Finset.singleton_subset_iff.mpr (hJ he))) _

/-- The graph-specific relative-progress conclusion at an actual current
state. The comparison-existence interface will be instantiated by exopt. -/
theorem state_progress (G : V → V → Prop) (w : V → V → ℝ≥0)
    (H : Finset (V × V)) (hH : H ⊆ candidates G) (h B β : ℕ) (hB : 2 * B ≤ β)
    (hcompare : ∀ w' : V → V → ℝ≥0,
      ∃ J : Finset (V × V), J ⊆ candidates (augment G H) ∧ J.card ≤ h ∧
        ∀ s t, Reachable (augment G H) s t →
          hopDistance (augment (augment G H) J) (augmentWeight (augment G H) w' J) s t ≤ B)
    (hpos : 0 < potential G w β H) :
    ∃ e ∈ candidates G, potential G w β H ≤ (2 * h) * (potential G w β H - potential G w β (insert e H)) := by
  obtain ⟨w', _, hc⟩ := exists_unique_minhop_reweighting (augment G H) (augmentWeight G w H)
  obtain ⟨J, hJ, hcard, hb⟩ := hcompare w'
  obtain ⟨e, he, hg⟩ := transfer_comparison (augment G H) (augmentWeight G w H) w' hc J hJ B β hB hb
    (by simpa only [potential_current G w β H hH] using hpos)
  rw [potential_current G w β H hH, potential_current_insert G w β H hH e] at hg
  refine ⟨e, ?_, hg.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hcard))⟩
  rw [← candidates_augment G H hH]
  exact hJ he

end GreedyShortcuts.WeightedStateProgress
