import LengthExpander.DensityBound
import Mathlib.Algebra.Order.Floor.Ring

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LengthExpander
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V W : Type*} {G : SimpleGraph V}

/-- Restricting vertices preserves the actual matching and earlier-walk model. -/
theorem parallelGreedy_comap {index : Sym2 V → ℕ} {s : ℕ}
    (H : IsParallelGreedy G index s) (f : W → V) (hf : Function.Injective f) :
    IsParallelGreedy (G.comap f) (fun e => index (e.map f)) s := by
  constructor
  · intro u v z hu hv hi
    apply hf
    exact H.matching (f u) (f v) (f z) hu hv hi
  · intro u v huv p hp he
    apply H.earlierFar (f u) (f v) huv (p.map (SimpleGraph.Hom.comap f G))
    · simpa only [Walk.length_map] using hp
    · intro e he'
      rw [Walk.edges_map] at he'
      obtain ⟨d,hd,rfl⟩ := List.mem_map.mp he'
      exact he d hd

/-- A finite nonempty graph has a vertex of degree no larger than any proven
average-degree upper bound. -/
theorem exists_degree_le_real [Fintype V] [Nonempty V] (G : SimpleGraph V)
    (B : ℝ) (hb : 2 * (G.edgeFinset.card : ℝ) / Fintype.card V ≤ B) :
    ∃ v : V, (G.degree v : ℝ) ≤ B := by
  classical
  by_contra hn
  have hlt : ∀ v : V, B < (G.degree v : ℝ) := by
    intro v
    exact lt_of_not_ge (fun hv => hn ⟨v,hv⟩)
  have hsum := sum_lt_sum_of_nonempty (s := (univ : Finset V)) univ_nonempty
    (fun v _ => hlt v)
  have hdeg : (∑ v : V, (G.degree v : ℝ)) = 2 * (G.edgeFinset.card : ℝ) := by
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  rw [hdeg] at hsum
  have hnpos : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos (α := V)
  have hb' := (div_le_iff₀ hnpos).mp hb
  simp only [sum_const,card_univ,nsmul_eq_mul] at hsum
  nlinarith

variable [Fintype V]

/-- Every nonempty induced graph has a genuinely low-degree vertex, using the
ambient n in the uniform bound. This is the input for constructive elimination. -/
theorem hereditary_low_degree {index : Sym2 V → ℕ} {s : ℕ}
    (H : IsParallelGreedy G index s) (hs : 2 ≤ s)
    (S : Finset V) (hS : S.Nonempty) :
    ∃ v : S, ((G.induce (S : Set V)).degree v : ℝ) ≤
      8 * (s : ℝ) * (Fintype.card V : ℝ)^(2/(s : ℝ)) := by
  classical
  haveI : Nonempty S := hS.to_subtype
  have HH := parallelGreedy_comap H (Subtype.val : S → V) Subtype.val_injective
  have hb := uniform_average_degree_bound HH hs
  have hcard : (Fintype.card S : ℝ) ≤ Fintype.card V := by
    exact_mod_cast Fintype.card_le_of_injective (Subtype.val : S → V) Subtype.val_injective
  have hpow := Real.rpow_le_rpow (Nat.cast_nonneg (Fintype.card S)) hcard
    (by positivity : (0 : ℝ) ≤ 2/(s : ℝ))
  apply exists_degree_le_real (G.induce (S : Set V))
  exact hb.trans (mul_le_mul_of_nonneg_left hpow (by positivity))

end LengthExpander
