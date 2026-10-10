import GreedyShortcuts.ShortcutWalk
import GreedyShortcuts.FiniteCharging
import Mathlib.Data.Nat.Log

/-! The warm-up potential-reduction argument for actual unweighted directed
shortcut sets. This is the shortcut special case of Section 2.1, not the
weighted hopset theorem or the stronger DAG size theorem of Section 3.
-/
namespace GreedyShortcuts.WarmupUnweighted

open Finset DirectedPaths GraphGreedy ShortcutWalk

variable {V : Type*} [Fintype V] [DecidableEq V]

def repairMultiplicity (β : ℕ) : ℕ := (β / 4 + 1) ^ 2

def blockLength (n β : ℕ) : ℕ := n ^ 2 / repairMultiplicity β + 1

theorem demand_charge (G : V → V → Prop) (β : ℕ) (hβ : 4 ≤ β)
    (H : Finset (V × V)) (hH : H ⊆ candidates G) (d : V × V) (hd : d ∈ candidates G) :
    repairMultiplicity β * contribution β (hopDist (augment G H) d.1 d.2) ≤
      ∑ e ∈ candidates G,
        (contribution β (hopDist (augment G H) d.1 d.2) -
          contribution β (hopDist (augment G (insert e H)) d.1 d.2)) := by
  by_cases hactive : β < hopDist (augment G H) d.1 d.2
  · have hr := reachable_augment G H ((mem_candidates G d).mp hd).2
    let p := canonical (augment G H) d.1 d.2 hr
    have hp := canonical_optimal (augment G H) d.1 d.2 hr
    have hL : β < p.length := by simpa only [hopDist_eq _ hr] using hactive
    have hc : (repairEdges p β).card = (β / 4 + 1) ^ 2 :=
      repairEdges_card hp.2.1 β hβ hL
    have hsub := repairEdges_subset hH hp.1 hp.2.1 β hβ hL
    have hrepair : ∀ e ∈ repairEdges p β,
        contribution β (hopDist (augment G (insert e H)) d.1 d.2) = 0 := by
      intro e he
      exact (contribution_eq_zero β _).mpr (repairEdges_repair hp.1 hp.2.1 β hβ hL he)
    have hh := FiniteCharging.repair_charge (candidates G) (repairEdges p β) hsub
      (contribution β (hopDist (augment G H) d.1 d.2))
      (fun e => contribution β (hopDist (augment G (insert e H)) d.1 d.2)) hrepair
    simpa only [hc, repairMultiplicity] using hh
  · have hz := (contribution_eq_zero β _).mpr (Nat.le_of_not_gt hactive)
    rw [hz, Nat.mul_zero]
    exact Nat.zero_le _

/-- Double count repaired demands and choose one real closure edge. -/
theorem averaged_progress (G : V → V → Prop) (β : ℕ) (hβ : 4 ≤ β)
    (H : Finset (V × V)) (hH : H ⊆ candidates G) (hpos : 0 < potential G β H) :
    ∃ e ∈ candidates G,
      repairMultiplicity β * potential G β H ≤
        (Fintype.card V) ^ 2 * (potential G β H - potential G β (insert e H)) := by
  have hC : (candidates G).Nonempty := by
    obtain ⟨e, he, _⟩ := potential_progress G β (by omega) H hpos
    exact ⟨e, he⟩
  obtain ⟨e, he, hg⟩ := FiniteCharging.exists_large_drop (candidates G) (candidates G) hC
    (fun d => contribution β (hopDist (augment G H) d.1 d.2))
    (fun e d => contribution β (hopDist (augment G (insert e H)) d.1 d.2))
    (repairMultiplicity β)
    (fun e _ d hd => contribution_mono β (hopDist_augment_antitone G
      (Finset.subset_insert e H) ((mem_candidates G d).mp hd).2))
    (demand_charge G β hβ H hH)
  exact ⟨e, he, hg.trans (Nat.mul_le_mul_right _ (candidates_card_le G))⟩

theorem relative_progress (G : V → V → Prop) (β : ℕ) (hβ : 4 ≤ β)
    (H : Finset (V × V)) (hH : H ⊆ candidates G) (hpos : 0 < potential G β H) :
    ∃ e ∈ candidates G, potential G β H ≤
      blockLength (Fintype.card V) β * (potential G β H - potential G β (insert e H)) := by
  obtain ⟨e, he, hg⟩ := averaged_progress G β hβ H hH hpos
  refine ⟨e, he, FiniteCharging.relative_progress _ _ _ _ ?_ hg⟩
  unfold repairMultiplicity
  positivity

/-- Explicit finite logarithmic warm-up size bound for the actual Algorithm 1
output, with no unproved graph-specific progress premise. -/
theorem output_card_bound (G : V → V → Prop) (β : ℕ) (hβ : 4 ≤ β) :
    (output G β (by omega)).card ≤
      (Nat.log 2 ((Fintype.card V) ^ 3) + 1) * blockLength (Fintype.card V) β := by
  apply output_card_of_relative_progress G β (by omega)
    (blockLength (Fintype.card V) β) (Nat.log 2 ((Fintype.card V) ^ 3) + 1)
  · exact Nat.zero_lt_succ _
  · exact relative_progress G β hβ
  · exact Nat.lt_pow_succ_log_self (by decide) _

end GreedyShortcuts.WarmupUnweighted
