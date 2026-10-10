import LightEFTSpanners.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Tactic

namespace LightEFTSpanners.BipartiteForcing
open SimpleGraph LightSpanners
variable {L R : Type*}

/-- Unit weights turn the actual walk weight into its edge count. -/
theorem unit_walk_weight {H : SimpleGraph (L⊕R)} {u v : L⊕R} (p : H.Walk u v) :
    walkWeight (fun _ => (1:ℝ)) p = p.length := by simp [walkWeight]

/-- A bipartite walk from opposite sides of length less than three must consist
of the direct edge. This is an actual walk argument, without a girth oracle. -/
theorem short_walk_implies_adj {H : SimpleGraph (L⊕R)}
    (hHG : H ≤ completeBipartiteGraph L R) {a : L} {b : R}
    (p : H.Walk (Sum.inl a) (Sum.inr b)) (hlen : p.length < 3) :
    H.Adj (Sum.inl a) (Sum.inr b) := by
  cases p with
  | @cons _ z _ h p =>
    cases z with
    | inl x => simpa using hHG h
    | inr y =>
      cases p with
      | nil => exact h
      | @cons _ z _ h' p =>
        cases z with
        | inr x => simpa using hHG h'
        | inl x =>
          have hz : p.length=0 := by simp only [Walk.length_cons] at hlen; omega
          have heq := Walk.eq_of_length_eq_zero hz
          simp at heq

/-- Every subgraph spanner with stretch below three of a complete bipartite
graph retains all edges. Only the empty fault set is needed for this lower bound. -/
theorem eft_eq {H : SimpleGraph (L⊕R)} {t : ℝ} {f : ℕ}
    (ht : t < 3) (h : IsEFTSpanner (completeBipartiteGraph L R) H (fun _ => 1) t f) :
    H = completeBipartiteGraph L R := by
  apply le_antisymm h.1
  have hs : IsSpanner (completeBipartiteGraph L R) H (fun _ => 1) t := by
    simpa [afterFaults] using h.2 ∅ (by simp)
  have edge (a : L) (b : R) : H.Adj (Sum.inl a) (Sum.inr b) := by
    have hadj : (completeBipartiteGraph L R).Adj (Sum.inl a) (Sum.inr b) := by simp
    obtain ⟨q,hq⟩ := hs.2 _ _ hadj.toWalk
    have hlen : q.length < 3 := by
      rw [unit_walk_weight] at hq
      simp [SimpleGraph.Adj.toWalk,walkWeight] at hq
      have hh : (q.length : ℝ) < 3 := lt_of_le_of_lt hq ht
      exact_mod_cast hh
    exact short_walk_implies_adj h.1 q hlen
  intro u v huv
  cases u with
  | inl a =>
    cases v with
    | inl a' => simpa using huv
    | inr b => exact edge a b
  | inr b =>
    cases v with
    | inl a => exact (edge a b).symm
    | inr b' => simpa using huv

end LightEFTSpanners.BipartiteForcing
