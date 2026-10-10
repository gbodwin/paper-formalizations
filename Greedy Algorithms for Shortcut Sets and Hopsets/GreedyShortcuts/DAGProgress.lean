import GreedyShortcuts.LightCharging
import Mathlib.Data.Nat.Log

/-! The actual heavy/light progress dichotomy and a parameterized finite
size theorem for the unweighted DAG greedy algorithm. -/
namespace GreedyShortcuts.DAGProgress

open Finset SimpleGraph DirectedPaths CanonicalSegments CanonicalSuffixPath
open LinearDistancePreservers.ConsistentTiebreaking
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem degree_partition {s t : V} (G : V → V → Prop) (β σ : ℕ) (q : DWalk s t) :
    (∑ v ∈ q.support.toFinset,degree G β v) =
      HeavyCharging.weight G β σ q + LightCharging.weight G β σ q := by
  classical
  rw [show (∑ v ∈ q.support.toFinset,degree G β v) =
    ∑ d : active G β,(q.support.toFinset ∩ SuffixIncidence.vertices (path G β d)).card from
    SuffixIncidence.degree_sum_intersections (path G β) (fun d => (path_optimal G β d).2.1) _]
  unfold HeavyCharging.weight LightCharging.weight HeavyCharging.heavy LightCharging.light
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  split_ifs <;> omega

/-- Source Section 3's dichotomy, with all graph geometry discharged and
explicit integer constants. -/
theorem local_dichotomy {G : V → V → Prop} (hG : Acyclic G)
    (β σ : ℕ) (hβ : 8 ≤ β) (hσ : 8 ≤ σ) (hpos : 0 < potential G β) :
    ∃ e ∈ candidates G,
      σ*potential G β ≤ 512*Fintype.card V*HeavyCharging.totalDrop G β e ∨
      β^3*potential G β ≤ 16384*σ*(Fintype.card V)^2*HeavyCharging.totalDrop G β e := by
  obtain ⟨s,t,q,hq,hshort,hscore⟩ := exists_high_score_path G β hβ hpos
  rw [degree_partition G β σ q] at hscore
  have hcase : HeavyCharging.weight G β σ q + LightCharging.weight G β σ q ≤
      2*HeavyCharging.weight G β σ q ∨
      HeavyCharging.weight G β σ q + LightCharging.weight G β σ q ≤
      2*LightCharging.weight G β σ q := by omega
  rcases hcase with hh | hl
  · obtain ⟨e,he,hbound⟩ := HeavyCharging.heavy_relative hG hq β σ hβ hσ hshort hpos
      (by have hm := Nat.mul_le_mul_left (256*Fintype.card V) hh; nlinarith)
    exact ⟨e,he,Or.inl hbound⟩
  · obtain ⟨e,he,hbound⟩ := LightCharging.light_relative hq.1 β σ hβ hshort hpos
      (by have hm := Nat.mul_le_mul_left (256*Fintype.card V) hl; nlinarith)
    exact ⟨e,he,Or.inr hbound⟩

def blockLength (n β σ : ℕ) : ℕ := max (512*n/σ+1) (16384*σ*n^2/β^3+1)

theorem augment_singleton (G : V → V → Prop) (H : Finset (V × V)) (e : V × V) :
    augment (augment G H) {e} = augment G (insert e H) := by
  funext u v
  apply propext
  simp [augment,or_assoc,or_left_comm,or_comm]

theorem current_drop (G : V → V → Prop) (β : ℕ) (H : Finset (V × V))
    (hH : H ⊆ candidates G) (e : V × V) :
    HeavyCharging.totalDrop (augment G H) β e =
      GraphGreedy.potential G β H - GraphGreedy.potential G β (insert e H) := by
  have hc : candidates (augment G H) = candidates G := by
    ext d
    simp only [mem_candidates,reachable_augment_iff G H hH]
  unfold HeavyCharging.totalDrop
  rw [potential_current_eq G β H hH]
  simp only [GraphGreedy.potential,hc,augment_singleton]

theorem relative_progress {G : V → V → Prop} (hG : Acyclic G)
    (β σ : ℕ) (hβ : 8 ≤ β) (hσ : 8 ≤ σ)
    (H : Finset (V × V)) (hH : H ⊆ candidates G) (hpos : 0 < GraphGreedy.potential G β H) :
    ∃ e ∈ candidates G, GraphGreedy.potential G β H ≤
      blockLength (Fintype.card V) β σ *
        (GraphGreedy.potential G β H - GraphGreedy.potential G β (insert e H)) := by
  obtain ⟨e,he,hcase⟩ := local_dichotomy (acyclic_augment hG hH) β σ hβ hσ
    (by simpa only [potential_current_eq G β H hH] using hpos)
  have he' : e ∈ candidates G := by
    simpa only [mem_candidates,reachable_augment_iff G H hH] using he
  simp only [potential_current_eq G β H hH,current_drop G β H hH e] at hcase
  refine ⟨e,he',?_⟩
  rcases hcase with hh | hl
  · exact (FiniteCharging.relative_progress _ _ _ _ (by omega) hh).trans
      (Nat.mul_le_mul_right _ (le_max_left _ _))
  · exact (FiniteCharging.relative_progress _ _ _ _ (by positivity) hl).trans
      (Nat.mul_le_mul_right _ (le_max_right _ _))

/-- A finite parameterized DAG size theorem for the actual greedy output.
No graph-progress or shortcut-size hypothesis is assumed. The balancing
choice of σ and the real-exponent presentation are separate arithmetic. -/
theorem output_card_bound {G : V → V → Prop} (hG : Acyclic G)
    (β σ : ℕ) (hβ : 8 ≤ β) (hσ : 8 ≤ σ) :
    (GraphGreedy.output G β (by omega)).card ≤
      (Nat.log 2 ((Fintype.card V)^3)+1)*blockLength (Fintype.card V) β σ := by
  apply GraphGreedy.output_card_of_relative_progress G β (by omega)
    (blockLength (Fintype.card V) β σ) (Nat.log 2 ((Fintype.card V)^3)+1)
  · exact lt_of_lt_of_le (Nat.zero_lt_succ _) (le_max_left _ _)
  · exact relative_progress hG β σ hβ hσ
  · exact Nat.lt_pow_succ_log_self (by decide) _

end GreedyShortcuts.DAGProgress
