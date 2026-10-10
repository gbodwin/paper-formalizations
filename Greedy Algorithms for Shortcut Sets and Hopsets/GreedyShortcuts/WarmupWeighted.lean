import GreedyShortcuts.WeightedShortcut
import GreedyShortcuts.WeightedGreedy
import GreedyShortcuts.CanonicalSegments
import GreedyShortcuts.WarmupBound

/-! Section 2.1's warm-up for the actual nonnegative weighted directed-graph
greedy algorithm. Every charged replacement remains a shortest weighted walk.
The stronger existentially optimal bound of Theorem 1.7 is not claimed here. -/
namespace GreedyShortcuts.WarmupWeighted

open Finset DirectedPaths WeightedPaths WeightedGreedy ShortcutWalk CanonicalSegments
open GraphGreedy (contribution contribution_eq_zero contribution_mono candidates_card_le)
open WarmupUnweighted (repairMultiplicity blockLength)
open scoped NNReal
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem repairEdges_repair_weighted {G : V → V → Prop} {w : V → V → ℝ≥0}
    {H : Finset (V × V)} (hH : H ⊆ candidates G) {s t : V} {p : DWalk s t}
    (hp : MinHopShortest (augment G H) (augmentWeight G w H) p)
    (β : ℕ) (hβ : 4 ≤ β) (hL : β < p.length) {e : V × V}
    (he : e ∈ repairEdges p β) :
    hopDistance (augment G (insert e H)) (augmentWeight G w (insert e H)) s t ≤ β := by
  obtain ⟨ij, hij, rfl⟩ := Finset.mem_image.mp he
  have hi := rectangle_indices hβ hL hij
  have hh := hop_after_subwalk_state hH hp.1 (segment_isSubwalk p ij.1 ij.2 hi.1.le)
    (vertices_ne hp.isPath hi.1 hi.2.1)
  rw [segment_length p hi.1.le hi.2.1] at hh
  dsimp only [edgeAt]
  omega

theorem demand_charge (G : V → V → Prop) (w : V → V → ℝ≥0) (β : ℕ) (hβ : 4 ≤ β)
    (H : Finset (V × V)) (hH : H ⊆ candidates G) (d : V × V) (hd : d ∈ candidates G) :
    repairMultiplicity β * contribution β (hopDistance (augment G H) (augmentWeight G w H) d.1 d.2) ≤
      ∑ e ∈ candidates G,
        (contribution β (hopDistance (augment G H) (augmentWeight G w H) d.1 d.2) -
          contribution β (hopDistance (augment G (insert e H)) (augmentWeight G w (insert e H)) d.1 d.2)) := by
  by_cases hactive : β < hopDistance (augment G H) (augmentWeight G w H) d.1 d.2
  · have hr := reachable_augment G H ((mem_candidates G d).mp hd).2
    let p := minHopPath (augment G H) (augmentWeight G w H) d.1 d.2 hr
    have hp := minHopPath_spec (augment G H) (augmentWeight G w H) d.1 d.2 hr
    have hL : β < p.length := by simpa only [hopDistance_eq _ _ hr] using hactive
    have hc : (repairEdges p β).card = (β / 4 + 1) ^ 2 := repairEdges_card hp.isPath β hβ hL
    have hsub := repairEdges_subset hH hp.1.1 hp.isPath β hβ hL
    have hrepair : ∀ e ∈ repairEdges p β,
        contribution β (hopDistance (augment G (insert e H)) (augmentWeight G w (insert e H)) d.1 d.2) = 0 := by
      intro e he
      exact (contribution_eq_zero β _).mpr (repairEdges_repair_weighted hH hp β hβ hL he)
    have hh := FiniteCharging.repair_charge (candidates G) (repairEdges p β) hsub
      (contribution β (hopDistance (augment G H) (augmentWeight G w H) d.1 d.2))
      (fun e => contribution β (hopDistance (augment G (insert e H))
        (augmentWeight G w (insert e H)) d.1 d.2)) hrepair
    simpa only [hc, repairMultiplicity] using hh
  · have hz := (contribution_eq_zero β _).mpr (Nat.le_of_not_gt hactive)
    rw [hz, Nat.mul_zero]
    exact Nat.zero_le _

theorem averaged_progress (G : V → V → Prop) (w : V → V → ℝ≥0) (β : ℕ) (hβ : 4 ≤ β)
    (H : Finset (V × V)) (hH : H ⊆ candidates G) (hpos : 0 < potential G w β H) :
    ∃ e ∈ candidates G, repairMultiplicity β * potential G w β H ≤
      (Fintype.card V) ^ 2 * (potential G w β H - potential G w β (insert e H)) := by
  have hC : (candidates G).Nonempty := by
    obtain ⟨e, he, _⟩ := potential_progress G w β (by omega) H hH hpos
    exact ⟨e, he⟩
  obtain ⟨e, he, hg⟩ := FiniteCharging.exists_large_drop (candidates G) (candidates G) hC
    (fun d => contribution β (hopDistance (augment G H) (augmentWeight G w H) d.1 d.2))
    (fun e d => contribution β (hopDistance (augment G (insert e H))
      (augmentWeight G w (insert e H)) d.1 d.2)) (repairMultiplicity β)
    (fun e he d hd => contribution_mono β (hopDistance_augment_mono G w hH
      (Finset.insert_subset he hH) (Finset.subset_insert e H) ((mem_candidates G d).mp hd).2))
    (demand_charge G w β hβ H hH)
  exact ⟨e, he, hg.trans (Nat.mul_le_mul_right _ (candidates_card_le G))⟩

theorem relative_progress (G : V → V → Prop) (w : V → V → ℝ≥0) (β : ℕ) (hβ : 4 ≤ β)
    (H : Finset (V × V)) (hH : H ⊆ candidates G) (hpos : 0 < potential G w β H) :
    ∃ e ∈ candidates G, potential G w β H ≤
      blockLength (Fintype.card V) β * (potential G w β H - potential G w β (insert e H)) := by
  obtain ⟨e, he, hg⟩ := averaged_progress G w β hβ H hH hpos
  refine ⟨e, he, FiniteCharging.relative_progress _ _ _ _ ?_ hg⟩
  unfold repairMultiplicity
  positivity

theorem output_card_bound (G : V → V → Prop) (w : V → V → ℝ≥0) (β : ℕ) (hβ : 4 ≤ β) :
    (output G w β (by omega)).card ≤
      (Nat.log 2 ((Fintype.card V) ^ 3) + 1) * blockLength (Fintype.card V) β := by
  apply (system G w β (by omega)).final_card_of_relative_progress
    (blockLength (Fintype.card V) β) (Nat.log 2 ((Fintype.card V) ^ 3) + 1)
    (Nat.zero_lt_succ _)
  · intro S hpos
    exact relative_progress G w β hβ S.1 S.2 hpos
  · exact (potential_le_cube G w β ∅).trans_lt (Nat.lt_pow_succ_log_self (by decide) _)

/-- Explicit finite warm-up bound for every positive hop target, under the
nonnegative-real-weight convention. No potential-progress premise is assumed. -/
theorem output_card_bound_all (G : V → V → Prop) (w : V → V → ℝ≥0) (β : ℕ) (hβ : 1 ≤ β) :
    (output G w β hβ).card ≤
      (Nat.log 2 ((Fintype.card V) ^ 3) + 1) * (16 * (Fintype.card V) ^ 2 / β ^ 2 + 1) := by
  by_cases hlarge : 4 ≤ β
  · exact (output_card_bound G w β hlarge).trans
      (Nat.mul_le_mul_left _ (WarmupBound.blockLength_le _ _ (by omega)))
  · have hs : β ^ 2 ≤ 16 := by nlinarith
    have hm := Nat.mul_le_mul_left ((Fintype.card V) ^ 2) hs
    have hdiv : (Fintype.card V) ^ 2 ≤ 16 * (Fintype.card V) ^ 2 / β ^ 2 := by
      apply (Nat.le_div_iff_mul_le (show 0 < β ^ 2 by positivity)).mpr
      simpa [Nat.mul_comm] using hm
    calc
      (output G w β hβ).card ≤ (Fintype.card V) ^ 2 := output_card_le G w β hβ
      _ ≤ 16 * (Fintype.card V) ^ 2 / β ^ 2 + 1 := by omega
      _ ≤ (Nat.log 2 ((Fintype.card V) ^ 3) + 1) *
          (16 * (Fintype.card V) ^ 2 / β ^ 2 + 1) := Nat.le_mul_of_pos_left _ (by omega)

end GreedyShortcuts.WarmupWeighted
