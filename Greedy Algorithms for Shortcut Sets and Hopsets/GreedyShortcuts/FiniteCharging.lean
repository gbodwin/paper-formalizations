import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-! Finite double counting for sum-potential greedy. A demand repaired by many
individual choices contributes its full current value to each such choice.
-/
namespace GreedyShortcuts.FiniteCharging

open Finset
variable {E D : Type*} [DecidableEq E] [DecidableEq D]

theorem repair_charge (C R : Finset E) (hRC : R ⊆ C) (f : ℕ) (g : E → ℕ)
    (hz : ∀ e ∈ R, g e = 0) :
    R.card * f ≤ ∑ e ∈ C, (f - g e) := by
  calc
    R.card * f = ∑ _e ∈ R, f := by simp
    _ = ∑ e ∈ R, (f - g e) := Finset.sum_congr rfl (fun e he => by rw [hz e he, Nat.sub_zero])
    _ ≤ ∑ e ∈ C, (f - g e) := Finset.sum_le_sum_of_subset hRC

/-- An exact finite averaging statement with no probability or division. -/
theorem exists_large_drop (C : Finset E) (Q : Finset D) (hC : C.Nonempty)
    (f : D → ℕ) (g : E → D → ℕ) (r : ℕ)
    (hle : ∀ e ∈ C, ∀ d ∈ Q, g e d ≤ f d)
    (hrow : ∀ d ∈ Q, r * f d ≤ ∑ e ∈ C, (f d - g e d)) :
    ∃ e ∈ C,
      r * (∑ d ∈ Q, f d) ≤ C.card * ((∑ d ∈ Q, f d) - ∑ d ∈ Q, g e d) := by
  let drop := fun e => (∑ d ∈ Q, f d) - ∑ d ∈ Q, g e d
  obtain ⟨e, he, hmax⟩ := Finset.exists_max_image C drop hC
  refine ⟨e, he, ?_⟩
  calc
    r * (∑ d ∈ Q, f d) = ∑ d ∈ Q, r * f d := Finset.mul_sum _ _ _
    _ ≤ ∑ d ∈ Q, ∑ e ∈ C, (f d - g e d) := Finset.sum_le_sum hrow
    _ = ∑ e ∈ C, ∑ d ∈ Q, (f d - g e d) := Finset.sum_comm
    _ = ∑ e ∈ C, drop e := by
      apply Finset.sum_congr rfl
      intro e he
      exact Finset.sum_tsub_distrib Q (hle e he)
    _ ≤ ∑ _e ∈ C, drop e := Finset.sum_le_sum (fun x hx => hmax x hx)
    _ = C.card * drop e := by simp

/-- Turn a multiplicative averaged estimate into the integer denominator used
by the exact potential-halving theorem. -/
theorem relative_progress (P Δ N r : ℕ) (hr : 0 < r) (h : r * P ≤ N * Δ) :
    P ≤ (N / r + 1) * Δ := by
  have hN : N ≤ r * (N / r + 1) := by
    have hm := Nat.mod_lt N hr
    have he := Nat.mod_add_div N r
    nlinarith
  have hh := h.trans (Nat.mul_le_mul_right Δ hN)
  have hh' : r * P ≤ r * ((N / r + 1) * Δ) := by simpa [Nat.mul_assoc] using hh
  nlinarith

end GreedyShortcuts.FiniteCharging
