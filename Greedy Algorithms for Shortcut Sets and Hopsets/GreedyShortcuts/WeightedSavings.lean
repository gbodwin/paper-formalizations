import GreedyShortcuts.WeightedExpansion
import GreedyShortcuts.WeightedGreedy

/-! A direct expansion proof of Lemma 4.3's multi-edge savings inequality.
No erroneous telescoping sign or unconditional endpoint summand is used. -/
namespace GreedyShortcuts.WeightedPaths

open SimpleGraph DirectedPaths Finset
open LinearDistancePreservers.ConsistentTiebreaking
open scoped NNReal
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem expansionLength_le (G : V → V → Prop) (w : V → V → ℝ≥0)
    (H : Finset (V × V)) (gain : V × V → ℕ) {s t : V} (q : DWalk s t)
    (hq : q.IsPath)
    (hgain : ∀ d ∈ q.darts, (d.fst,d.snd) ∈ H → hopDistance G w d.fst d.snd ≤ 1 + gain (d.fst,d.snd)) :
    expansionLength G w H q ≤ q.length + ∑ e ∈ H, gain e := by
  classical
  let F := q.darts.toFinset
  have hn := Walk.darts_nodup_of_support_nodup hq.support_nodup
  have hc : F.card = q.length := by simp [F, List.toFinset_card_of_nodup hn]
  have hsum : (∑ d ∈ F.filter (fun d => (d.fst,d.snd) ∈ H), gain (d.fst,d.snd)) ≤ ∑ e ∈ H, gain e := by
    apply Finset.sum_le_sum_of_injOn (fun d => (d.fst,d.snd))
    · intro a ha b hb he
      exact Dart.ext a b he
    · intro e he
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
      exact (Finset.mem_filter.mp hd).2
    · intro d hd
      exact le_rfl
    · intro e he hnot
      exact Nat.zero_le _
  calc
    expansionLength G w H q = ∑ d ∈ F, if (d.fst,d.snd) ∈ H then hopDistance G w d.fst d.snd else 1 :=
      (List.sum_toFinset _ hn).symm
    _ ≤ ∑ d ∈ F, (1 + if (d.fst,d.snd) ∈ H then gain (d.fst,d.snd) else 0) := by
      apply Finset.sum_le_sum
      intro d hd
      by_cases he : (d.fst,d.snd) ∈ H
      · simpa only [if_pos he] using hgain d (List.mem_toFinset.mp hd) he
      · simp [he]
    _ = q.length + ∑ d ∈ F.filter (fun d => (d.fst,d.snd) ∈ H), gain (d.fst,d.snd) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_filter]
      simp [hc]
    _ ≤ q.length + ∑ e ∈ H, gain e := Nat.add_le_add_left hsum _

/-- A unique original shortest path cannot receive more aggregate hop saving
from a hopset than the sum of the individual empty-state savings. -/
theorem multi_edge_savings {G : V → V → Prop} {w : V → V → ℝ≥0}
    {H : Finset (V × V)} (hH : H ⊆ candidates G)
    {s t : V} {p : DWalk s t} (hp : UniqueShortest G w p) :
    hopDistance G w s t ≤ hopDistance (augment G H) (augmentWeight G w H) s t +
      ∑ e ∈ H, (hopDistance G w s t -
        hopDistance (augment G {e}) (augmentWeight G w {e}) s t) := by
  have hr : Reachable G s t := ⟨p,hp.1.1⟩
  have ha := reachable_augment G H hr
  let q := minHopPath (augment G H) (augmentWeight G w H) s t ha
  have hq := minHopPath_spec (augment G H) (augmentWeight G w H) s t ha
  have hmin : MinHopShortest G w p := ⟨hp.1, fun z hz => by rw [hp.2 z hz]⟩
  have hlen := hmin.length_eq_hopDistance
  obtain ⟨hexpand, hsub⟩ := unique_expansion hH hp hq.1
  have hg : ∀ d ∈ q.darts, (d.fst,d.snd) ∈ H → hopDistance G w d.fst d.snd ≤
      1 + (hopDistance G w s t - hopDistance (augment G {(d.fst,d.snd)})
        (augmentWeight G w {(d.fst,d.snd)}) s t) := by
    intro d hd he
    have hne := ((mem_candidates G _).mp (hH he)).1
    have hx := hop_after_subwalk hp.1 (hsub d hd he) hne
    have hseg := (minHopPath_spec G w d.fst d.snd ((mem_candidates G _).mp (hH he)).2).length_eq_hopDistance
    rw [hseg, hlen] at hx
    omega
  have hh := expansionLength_le G w H
    (fun e => hopDistance G w s t - hopDistance (augment G {e}) (augmentWeight G w {e}) s t)
    q hq.isPath hg
  rw [← hexpand, hlen, hq.length_eq_hopDistance] at hh
  exact hh

end GreedyShortcuts.WeightedPaths
