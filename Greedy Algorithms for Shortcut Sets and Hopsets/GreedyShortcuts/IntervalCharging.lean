import GreedyShortcuts.FiniteCharging
import Mathlib.Order.Interval.Finset.Nat

/-! Exact finite interval and double-counting estimates for the heavy case.
These are arithmetic components; the actual graph witnesses remain separate. -/
namespace GreedyShortcuts.IntervalCharging

open Finset

def Convex (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c, a ≤ c → c ≤ b → c ∈ S

theorem convex_eq_Icc (S : Finset ℕ) (hS : S.Nonempty) (hc : Convex S) :
    S = Finset.Icc (S.min' hS) (S.max' hS) := by
  ext i
  constructor
  · intro hi
    exact Finset.mem_Icc.mpr ⟨S.min'_le i hi,S.le_max' i hi⟩
  · intro hi
    exact hc _ (S.min'_mem hS) _ (S.max'_mem hS) i
      (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2

def pairedStarts (S : Finset ℕ) (δ : ℕ) : Finset ℕ := S.filter (fun a => a+δ ∈ S)

theorem pairedStarts_interval (a b δ : ℕ) (h : a+δ ≤ b) :
    pairedStarts (Finset.Icc a b) δ = Finset.Icc a (b-δ) := by
  ext i
  simp only [pairedStarts,Finset.mem_filter,Finset.mem_Icc]
  omega

/-- At least half a heavy contiguous intersection starts a legal pair at
separation floor(σ/2). -/
theorem pairedStarts_heavy (S : Finset ℕ) (hc : Convex S) (σ : ℕ)
    (hσ : 8 ≤ σ) (hheavy : σ ≤ S.card) :
    S.card ≤ 2 * (pairedStarts S (σ/2)).card := by
  have hS : S.Nonempty := Finset.card_pos.mp (by omega)
  rw [convex_eq_Icc S hS hc] at hheavy ⊢
  have hmin := S.min'_le (S.max' hS) (S.max'_mem hS)
  have hcard := Nat.card_Icc (S.min' hS) (S.max' hS)
  have hsep : S.min' hS + σ/2 ≤ S.max' hS := by omega
  rw [pairedStarts_interval _ _ _ hsep]
  simp only [Nat.card_Icc]
  omega

theorem separation_saving (σ : ℕ) (hσ : 8 ≤ σ) : σ ≤ 4*(σ/2-1) := by omega

/-- Scaled finite averaging, allowing the row weights to be intersection
sizes while column weights are actual whole-potential drops. -/
theorem exists_scaled_column {I E : Type*} [DecidableEq I] [DecidableEq E]
    (Q : Finset I) (C : Finset E) (hC : C.Nonempty) (weight : I → ℕ)
    (charge : E → I → ℕ) (drop : E → ℕ) (r κ : ℕ)
    (hrow : ∀ i ∈ Q, r*weight i ≤ κ*∑ e ∈ C, charge e i)
    (hcolumn : ∀ e ∈ C, (∑ i ∈ Q, charge e i) ≤ drop e) :
    ∃ e ∈ C, r*(∑ i ∈ Q, weight i) ≤ κ*C.card*drop e := by
  obtain ⟨e,he,hm⟩ := Finset.exists_max_image C drop hC
  refine ⟨e,he,?_⟩
  calc
    r*(∑ i ∈ Q,weight i) = ∑ i ∈ Q,r*weight i := Finset.mul_sum _ _ _
    _ ≤ ∑ i ∈ Q,κ*∑ e ∈ C,charge e i := Finset.sum_le_sum hrow
    _ = κ*∑ e ∈ C,∑ i ∈ Q,charge e i := by rw [← Finset.mul_sum,Finset.sum_comm]
    _ ≤ κ*∑ e ∈ C,drop e := Nat.mul_le_mul_left κ (Finset.sum_le_sum hcolumn)
    _ ≤ κ*∑ _e ∈ C,drop e := Nat.mul_le_mul_left κ (Finset.sum_le_sum hm)
    _ = κ*C.card*drop e := by simp [Nat.mul_assoc]

end GreedyShortcuts.IntervalCharging
