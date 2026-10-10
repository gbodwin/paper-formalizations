import GreedyShortcuts.WeightedSavings
import GreedyShortcuts.FiniteCharging

/-! Unique-shortest-path progress from any comparison hopset of half the target
hopbound. The comparison hopset is explicit; the existential benchmark and
transfer from perturbed weights are separate obligations. -/
namespace GreedyShortcuts.WeightedProgress

open Finset DirectedPaths WeightedPaths
open GraphGreedy (contribution contribution_le contribution_mono)
open scoped NNReal
variable {V : Type*} [Fintype V] [DecidableEq V]

@[simp] theorem augment_empty_eq (G : V → V → Prop) : augment G ∅ = G := by
  funext s t
  simp [augment]

/-- Finite averaging with a scale on the sum of one-choice savings. -/
theorem scaled_averaging {E D : Type*} [DecidableEq E] [DecidableEq D]
    (C : Finset E) (Q : Finset D) (f : D → ℕ) (g : E → D → ℕ) (r : ℕ)
    (hle : ∀ e ∈ C, ∀ d ∈ Q, g e d ≤ f d)
    (hrow : ∀ d ∈ Q, f d ≤ r * ∑ e ∈ C, (f d - g e d))
    (hpos : 0 < ∑ d ∈ Q, f d) :
    ∃ e ∈ C, (∑ d ∈ Q, f d) ≤ r * C.card * ((∑ d ∈ Q, f d) - ∑ d ∈ Q, g e d) := by
  have htotal : (∑ d ∈ Q, f d) ≤ r * ∑ e ∈ C, ((∑ d ∈ Q, f d) - ∑ d ∈ Q, g e d) := by
    calc
      (∑ d ∈ Q, f d) ≤ ∑ d ∈ Q, r * ∑ e ∈ C, (f d - g e d) := Finset.sum_le_sum hrow
      _ = r * ∑ e ∈ C, ∑ d ∈ Q, (f d - g e d) := by rw [← Finset.mul_sum, Finset.sum_comm]
      _ = _ := by
        congr 1
        apply Finset.sum_congr rfl
        intro e he
        exact Finset.sum_tsub_distrib Q (hle e he)
  have hC : C.Nonempty := by
    by_contra hn
    have hz := Finset.not_nonempty_iff_eq_empty.mp hn
    have hzsum : (∑ d ∈ Q, f d) = 0 := by simpa [hz] using htotal
    exact (Nat.ne_of_gt hpos) hzsum
  obtain ⟨e, he, hm⟩ := Finset.exists_max_image C
    (fun e => (∑ d ∈ Q, f d) - ∑ d ∈ Q, g e d) hC
  refine ⟨e, he, htotal.trans ?_⟩
  calc
    r * ∑ e ∈ C, ((∑ d ∈ Q, f d) - ∑ d ∈ Q, g e d)
      ≤ r * ∑ _e ∈ C, ((∑ d ∈ Q, f d) - ∑ d ∈ Q, g e d) :=
        Nat.mul_le_mul_left r (Finset.sum_le_sum hm)
    _ = _ := by simp [Nat.mul_assoc]

/-- A comparison hopset reaching half the greedy target yields an individual
candidate drop at least the current potential divided by twice its size. -/
theorem comparison_progress (G : V → V → Prop) (w : V → V → ℝ≥0)
    (hunique : ∀ s t, Reachable G s t → ∃ p : DWalk s t, UniqueShortest G w p)
    (H : Finset (V × V)) (hH : H ⊆ candidates G) (B β : ℕ) (hB : 2 * B ≤ β)
    (hbound : ∀ s t, Reachable G s t →
      hopDistance (augment G H) (augmentWeight G w H) s t ≤ B)
    (hpos : 0 < WeightedGreedy.potential G w β ∅) :
    ∃ e ∈ H, WeightedGreedy.potential G w β ∅ ≤
      (2 * H.card) * (WeightedGreedy.potential G w β ∅ - WeightedGreedy.potential G w β {e}) := by
  let f := fun d : V × V => contribution β (hopDistance G w d.1 d.2)
  let g := fun (e d : V × V) => contribution β
    (hopDistance (augment G {e}) (augmentWeight G w {e}) d.1 d.2)
  have hle : ∀ e ∈ H, ∀ d ∈ candidates G, g e d ≤ f d := by
    intro e he d hd
    have hm := hopDistance_augment_mono G w (Finset.empty_subset _)
      (Finset.singleton_subset_iff.mpr (hH he)) (Finset.empty_subset _)
      ((mem_candidates G d).mp hd).2
    apply contribution_mono β
    simpa only [augment_empty_eq, augmentWeight_empty] using hm
  have hrow : ∀ d ∈ candidates G, f d ≤ 2 * ∑ e ∈ H, (f d - g e d) := by
    intro d hd
    by_cases hactive : β < hopDistance G w d.1 d.2
    · have hr := ((mem_candidates G d).mp hd).2
      obtain ⟨p, hp⟩ := hunique d.1 d.2 hr
      have hs := multi_edge_savings hH hp
      have hb := hbound d.1 d.2 hr
      have hraw : (∑ e ∈ H, (hopDistance G w d.1 d.2 -
          hopDistance (augment G {e}) (augmentWeight G w {e}) d.1 d.2)) ≤
          ∑ e ∈ H, (f d - g e d) := by
        apply Finset.sum_le_sum
        intro e he
        dsimp [f, g]
        rw [contribution, if_pos hactive]
        exact Nat.sub_le_sub_left (contribution_le β _) _
      have hf : f d = hopDistance G w d.1 d.2 := by simp [f, contribution, hactive]
      calc
        f d = hopDistance G w d.1 d.2 := hf
        _ ≤ 2 * ∑ e ∈ H, (f d - g e d) := by omega
    · have hf : f d = 0 := by simp [f, contribution, hactive]
      rw [hf]
      exact Nat.zero_le _
  have hpos' : 0 < ∑ d ∈ candidates G, f d := by
    simpa only [WeightedGreedy.potential, augment_empty_eq, augmentWeight_empty] using hpos
  obtain ⟨e, he, hh⟩ := scaled_averaging H (candidates G) f g 2 hle hrow hpos'
  refine ⟨e, he, ?_⟩
  simpa only [WeightedGreedy.potential, augment_empty_eq, augmentWeight_empty] using hh

end GreedyShortcuts.WeightedProgress
