import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-! Exact truncated-window counting. These windows include the truncated
windows at both ends; every position is covered exactly b times. This avoids
boundary exceptions in the suffix-window averaging argument. -/
namespace GreedyShortcuts.FiniteWindows

open Finset

def nodes (m b a : ℕ) : Finset ℕ :=
  (Finset.range m).filter fun j => j ≤ a ∧ a < j + b

def starts (m b j : ℕ) : Finset ℕ :=
  (Finset.range (m + b - 1)).filter fun a => j ≤ a ∧ a < j + b

theorem starts_eq (m b j : ℕ) (hj : j < m) : starts m b j = Finset.Ico j (j + b) := by
  ext a
  simp only [starts, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  omega

theorem starts_card (m b j : ℕ) (hj : j < m) : (starts m b j).card = b := by
  rw [starts_eq m b j hj, Nat.card_Ico]
  omega

theorem nodes_eq (m b a : ℕ) (hm : 0 < m) (hb : 0 < b)
    (ha : a < m + b - 1) : nodes m b a = Finset.Icc (a + 1 - b) (min a (m - 1)) := by
  ext j
  simp only [nodes, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  omega

theorem nodes_nonempty (m b a : ℕ) (hm : 0 < m) (hb : 0 < b)
    (ha : a < m + b - 1) : (nodes m b a).Nonempty := by
  rw [nodes_eq m b a hm hb ha]
  exact ⟨a + 1 - b, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩

theorem nodes_card_le (m b a : ℕ) (hm : 0 < m) (hb : 0 < b)
    (ha : a < m + b - 1) : (nodes m b a).card ≤ b := by
  rw [nodes_eq m b a hm hb ha, Nat.card_Icc]
  omega

def score (m b : ℕ) (weight : ℕ → ℕ) (a : ℕ) : ℕ :=
  ∑ j ∈ nodes m b a, weight j

theorem sum_scores (m b : ℕ) (weight : ℕ → ℕ) :
    (∑ a ∈ Finset.range (m + b - 1), score m b weight a) =
      b * ∑ j ∈ Finset.range m, weight j := by
  simp only [score, nodes, Finset.sum_filter]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hc := starts_card m b j (Finset.mem_range.mp hj)
  calc
    (∑ a ∈ Finset.range (m + b - 1), if j ≤ a ∧ a < j + b then weight j else 0) =
        ∑ _a ∈ starts m b j, weight j := by rw [starts, Finset.sum_filter]
    _ = b * weight j := by simp [hc]

theorem window_count_le (m b : ℕ) (hb : b ≤ m) : m + b - 1 ≤ 2 * m := by omega

section Incidence
variable {I V W : Type*} [DecidableEq I] [DecidableEq V] [Fintype V]

def degree (F : Finset I) (vertex : I → V) (v : V) : ℕ :=
  (F.filter fun i => vertex i = v).card

theorem degree_sum (F : Finset I) (vertex : I → V) :
    (∑ v, degree F vertex v) = F.card := by
  simpa [degree] using
    (Finset.card_eq_sum_card_fiberwise (s := F) (t := Finset.univ) (f := vertex)
      (fun _ _ => Finset.mem_univ _)).symm

theorem degree_square_sum (F : Finset I) (vertex : I → V) :
    (∑ v, (degree F vertex v) ^ 2) = ∑ i ∈ F, degree F vertex (vertex i) := by
  simpa [degree, pow_two] using Finset.sum_fiberwise' F vertex (degree F vertex)

theorem incidence_cauchy (F : Finset I) (vertex : I → V) :
    F.card ^ 2 ≤ Fintype.card V * ∑ i ∈ F, degree F vertex (vertex i) := by
  have hh := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset V)
    (fun _ => (1 : ℕ)) (degree F vertex)
  simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
    degree_sum, degree_square_sum] using hh

/-- The exact suffix-window averaging inequality after constructing windows
and their total-score/number bounds. The finite graph instantiation remains
separate from this arithmetic and incidence lemma. -/
theorem exists_high_score (F : Finset I) (vertex : I → V) (windows : Finset W)
    (weight : W → ℕ) (b : ℕ) (hb : 0 < b) (hF : 0 < F.card)
    (hcount : windows.card ≤ 2 * F.card)
    (htotal : b * (∑ i ∈ F, degree F vertex (vertex i)) ≤ ∑ w ∈ windows, weight w) :
    ∃ w ∈ windows, b * F.card ≤ 2 * Fintype.card V * weight w := by
  have hc := incidence_cauchy F vertex
  have hn : windows.Nonempty := by
    by_contra h
    have hz : windows = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    rw [hz, Finset.sum_empty] at htotal
    have hsum : (∑ i ∈ F, degree F vertex (vertex i)) = 0 := by nlinarith
    rw [hsum, Nat.mul_zero] at hc
    nlinarith
  obtain ⟨w, hw, hmax⟩ := Finset.exists_max_image windows weight hn
  refine ⟨w, hw, ?_⟩
  have hu : (∑ x ∈ windows, weight x) ≤ windows.card * weight w := by
    calc
      _ ≤ ∑ _x ∈ windows, weight w := Finset.sum_le_sum (fun x hx => hmax x hx)
      _ = _ := by simp
  have hm := Nat.mul_le_mul_right (weight w) hcount
  have hupper := htotal.trans (hu.trans hm)
  have hc' := Nat.mul_le_mul_left b hc
  have hu' := Nat.mul_le_mul_left (Fintype.card V) hupper
  have hmul : F.card * (b * F.card) ≤ F.card * (2 * Fintype.card V * weight w) := by
    nlinarith
  exact Nat.le_of_mul_le_mul_left hmul hF

end Incidence
end GreedyShortcuts.FiniteWindows
