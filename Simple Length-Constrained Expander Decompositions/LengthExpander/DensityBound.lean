import LengthExpander.FixedSizeSampling
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity

namespace LengthExpander
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- An explicit uniform version of the paper's density bound, with no roots or
asymptotic notation: m^r ≤ n (4nr)^r. The corresponding average degree is at
most 8r n^(1/r). This statement includes empty graphs and low density. -/
theorem uniform_density_power {index : Sym2 V → ℕ} {s r : ℕ}
    (H : IsParallelGreedy G index s) (hr : 0 < r) (hrs : 2*r ≤ s+1) :
    G.edgeFinset.card^r ≤ Fintype.card V * (4 * Fintype.card V * r)^r := by
  classical
  by_cases hne : Nonempty V
  · let := hne
    have hn : 0 < Fintype.card V := Fintype.card_pos
    by_cases hm : Fintype.card V*r ≤ G.edgeFinset.card
    · have hn2 : 2 ≤ Fintype.card V := by
        by_contra h
        have hn1 : Fintype.card V = 1 := by omega
        have hc : G.edgeFinset.card ≤ (Fintype.card V).choose 2 := by
          exact G.card_edgeFinset_le_card_choose_two
        rw [hn1, show (1 : ℕ).choose 2 = 0 by decide] at hc
        rw [hn1] at hm
        omega
      have hm2 : 2*r ≤ G.edgeFinset.card := (Nat.mul_le_mul_right r hn2).trans hm
      have hbase : G.edgeFinset.card ≤ 2 * (G.edgeFinset.card+1-r) := by omega
      have hpower := Nat.pow_le_pow_left hbase r
      have hd := parallelGreedy_density_polynomial H hr hrs hm
      have hd' : (G.edgeFinset.card+1-r)^r <
          2 * Fintype.card V * (Fintype.card V*r)^r :=
        (Nat.le_mul_of_pos_left _ hr).trans_lt hd
      have hpow2 : 2^(r+1) ≤ (4:ℕ)^r := by
        calc
          2^(r+1) ≤ 2^(2*r) := Nat.pow_le_pow_right (by decide) (by omega)
          _ = 4^r := by rw [pow_mul]; norm_num
      apply le_of_lt
      calc
        _ ≤ (2 * (G.edgeFinset.card+1-r))^r := hpower
        _ = 2^r * (G.edgeFinset.card+1-r)^r := by rw [mul_pow]
        _ < 2^r * (2 * Fintype.card V * (Fintype.card V*r)^r) :=
          Nat.mul_lt_mul_of_pos_left hd' (Nat.pow_pos (by decide))
        _ = 2^(r+1) * (Fintype.card V * (Fintype.card V*r)^r) := by rw [pow_succ]; ring
        _ ≤ 4^r * (Fintype.card V * (Fintype.card V*r)^r) :=
          Nat.mul_le_mul_right _ hpow2
        _ = Fintype.card V * (4 * Fintype.card V * r)^r := by
          rw [show 4 * Fintype.card V * r = 4 * (Fintype.card V*r) by ring, mul_pow]
          ring
    · have hbase : G.edgeFinset.card ≤ 4 * Fintype.card V * r := by nlinarith
      exact (Nat.pow_le_pow_left hbase r).trans (Nat.le_mul_of_pos_left _ hn)
  · have : IsEmpty V := not_nonempty_iff.mp hne
    have hG : G = ⊥ := by ext u; exact isEmptyElim u
    simp [hG, Nat.ne_of_gt hr]

/-- Explicit edge bound, taking the r-th root of the proved finite counting
inequality. No forest-cover conclusion is asserted by this theorem. -/
theorem uniform_edge_bound {index : Sym2 V → ℕ} {s r : ℕ}
    (H : IsParallelGreedy G index s) (hr : 0 < r) (hrs : 2*r ≤ s+1) :
    (G.edgeFinset.card : ℝ) ≤
      4 * (Fintype.card V : ℝ) * r * (Fintype.card V : ℝ)^((r : ℝ)⁻¹) := by
  have hb := uniform_density_power H hr hrs
  have hc : (G.edgeFinset.card : ℝ)^r ≤
      (Fintype.card V : ℝ) * (4 * (Fintype.card V : ℝ) * r)^r := by exact_mod_cast hb
  apply le_of_pow_le_pow_left₀ (Nat.ne_of_gt hr) (by positivity)
  rw [mul_pow,Real.rpow_inv_natCast_pow (Nat.cast_nonneg _) (Nat.ne_of_gt hr)]
  simpa only [mul_comm] using hc

/-- The advertised average-degree order, with an explicit universal constant.
Odd s uses r=(s+1)/2 automatically. -/
theorem uniform_average_degree_bound {index : Sym2 V → ℕ} {s : ℕ}
    (H : IsParallelGreedy G index s) (hs : 2 ≤ s) :
    2 * (G.edgeFinset.card : ℝ) / Fintype.card V ≤
      8 * (s : ℝ) * (Fintype.card V : ℝ)^(2 / (s : ℝ)) := by
  classical
  by_cases hne : Nonempty V
  · let := hne
    let r := (s+1)/2
    have hr : 0 < r := by dsimp [r]; omega
    have hrs : 2*r ≤ s+1 := by dsimp [r]; omega
    have hsr : s ≤ 2*r := by dsimp [r]; omega
    have hrs' : r ≤ s := by dsimp [r]; omega
    have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos (α := V)
    have hn1 : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast Fintype.card_pos (α := V)
    have hrr : (0 : ℝ) < r := by exact_mod_cast hr
    have hss : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
    have he : (r : ℝ)⁻¹ ≤ 2 / (s : ℝ) := by
      rw [inv_eq_one_div,div_le_div_iff₀ hrr hss]
      norm_num only [one_mul]
      exact_mod_cast hsr
    have hpow := Real.rpow_le_rpow_of_exponent_le hn1 he
    have hb := uniform_edge_bound H hr hrs
    apply (div_le_iff₀ hn).mpr
    have hrle : (r : ℝ) ≤ s := by exact_mod_cast hrs'
    have hp0 : 0 ≤ (Fintype.card V : ℝ)^((r : ℝ)⁻¹) := Real.rpow_nonneg hn.le _
    have hx := mul_le_mul hrle hpow hp0 (by positivity : (0 : ℝ) ≤ s)
    nlinarith
  · have : IsEmpty V := not_nonempty_iff.mp hne
    simp only [Fintype.card_of_isEmpty, Nat.cast_zero, div_zero]
    positivity

end LengthExpander
