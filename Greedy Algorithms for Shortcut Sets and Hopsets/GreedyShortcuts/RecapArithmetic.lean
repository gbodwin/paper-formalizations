import Mathlib.Tactic

/-!
Exact rounding for a repaired explanation of the cited BRR long-path rule.

These arithmetic facts do not prove the graph-level progress property and do
not give a log-free bound for the paper's sum-potential greedy algorithm.
The source map records the distinction and the remaining proof obligations.
-/

namespace GreedyShortcuts.RecapArithmetic

/-- Offset from each end of a path longer than the target hopbound. -/
def margin (β : ℕ) : ℕ := (β - 2) / 4

/-- The replacement route through the inserted edge fits below the half-target. -/
theorem margin_half (β : ℕ) (hβ : 8 ≤ β) :
    2 * (2 * margin β + 1) ≤ β := by
  unfold margin
  omega

/-- The two shortcut endpoints are separated by at least two path edges. -/
theorem margin_separated (β L : ℕ) (hβ : 8 ≤ β) (hL : β < L) :
    margin β + 1 < L - margin β := by
  unfold margin
  omega

/-- Every prefix-suffix pair counted in the progress rectangle was above the
half-target before insertion. This is an inequality about path indices;
identifying index differences with hopdistances is a separate graph lemma. -/
theorem rectangle_old_distance (β L i j : ℕ) (hβ : 8 ≤ β) (hL : β < L)
    (hi : i ≤ margin β) (hj : L - margin β ≤ j) :
    β < 2 * (j - i) := by
  unfold margin at *
  omega

/-- The explicit route using the inserted edge is at or below the half-target. -/
theorem rectangle_new_distance (β L i j : ℕ) (hβ : 8 ≤ β) (hL : β < L)
    (hi : i ≤ margin β) (hj : j ≤ L) :
    2 * ((margin β - i) + 1 + (j - (L - margin β))) ≤ β := by
  unfold margin at *
  omega

/-- The rectangle has at least β²/64 pairs, expressed without real division. -/
theorem rectangle_size (β : ℕ) (hβ : 8 ≤ β) :
    β ^ 2 ≤ 64 * (margin β + 1) ^ 2 := by
  have h : β ≤ 8 * (margin β + 1) := by
    unfold margin
    omega
  have hh := Nat.mul_self_le_mul_self h
  nlinarith

/-- The prefix-suffix index rectangle contains exactly the claimed number of
pairs. Its image consists of distinct vertex pairs when the selected path is simple. -/
theorem index_rectangle_card (β L : ℕ) (hβ : 8 ≤ β) (hL : β < L) :
    ((Finset.range (margin β + 1)).product
      (Finset.Icc (L - margin β) L)).card = (margin β + 1) ^ 2 := by
  rw [Finset.product_eq_sprod, Finset.card_product, Finset.card_range, Nat.card_Icc]
  have hm : margin β ≤ L := by
    unfold margin
    omega
  have heq : L + 1 - (L - margin β) = margin β + 1 := by omega
  rw [heq]
  ring

/-- Conditional counting corollary. The graph-level proof must establish that
`rounds` disjoint eliminations each remove this many pairs from at most n². -/
theorem rounds_bound (β n rounds : ℕ) (hβ : 8 ≤ β)
    (hprogress : rounds * (margin β + 1) ^ 2 ≤ n ^ 2) :
    rounds * β ^ 2 ≤ 64 * n ^ 2 := by
  have h := rectangle_size β hβ
  have hm := Nat.mul_le_mul_left rounds h
  nlinarith

/-- Numeric check for the seven-vertex directed-path source diagnostic.
This declaration alone does not encode the graph or prove its distance counts. -/
theorem seven_vertex_average : (6 : ℚ) < 40 / 3 := by
  norm_num

end GreedyShortcuts.RecapArithmetic
