import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Choose.Basic
import Lean.Elab.Tactic.Omega

/-! Exact finite parameter identities underlying the displayed asymptotic lower bound. -/

namespace DegreeFaultSpanners

/-- Number of vertices in the `f`-cloud blowup of the `k`-dimensional incidence graph. -/
def familyVertices (k p f : ℕ) : ℕ := 2 * f * p ^ k

/-- Number of edges in that actual cloud blowup. -/
def familyEdges (k p f : ℕ) : ℕ := f ^ 2 * p ^ (k + 1)

/-- The exact scaling identity; no unspecified asymptotic constants are assumed. -/
theorem family_scaling (k p f : ℕ) (hk : 1 ≤ k) :
    2 ^ (k + 1) * familyEdges k p f ^ k =
      f ^ (k - 1) * familyVertices k p f ^ (k + 1) := by
  have hexp : k - 1 + (k + 1) = 2 * k := by omega
  simp only [familyEdges, familyVertices, mul_pow, ← pow_mul]
  calc
    2 ^ (k + 1) * (f ^ (2 * k) * p ^ ((k + 1) * k)) =
        2 ^ (k + 1) * ((f ^ (k - 1) * f ^ (k + 1)) * p ^ (k * (k + 1))) := by
      rw [← pow_add, hexp, Nat.mul_comm (k + 1) k]
    _ = f ^ (k - 1) * (2 ^ (k + 1) * f ^ (k + 1) * p ^ (k * (k + 1))) := by ring

/-- A uniform explicit constant in the integer-power lower-bound formulation. -/
theorem family_power_lower_bound (k p f : ℕ) (hk : 1 ≤ k) :
    f ^ (k - 1) * familyVertices k p f ^ (k + 1) ≤
      4 ^ k * familyEdges k p f ^ k := by
  rw [← family_scaling k p f hk]
  apply Nat.mul_le_mul_right
  calc
    2 ^ (k + 1) ≤ 2 ^ (2 * k) := Nat.pow_le_pow_right (by decide) (by omega)
    _ = 4 ^ k := by rw [pow_mul]; norm_num

/-- Increasing prime parameters produces unbounded graph sizes. -/
theorem familyVertices_ge_parameter (k p f : ℕ) (hk : 1 ≤ k)
    (hp : 1 ≤ p) (hf : 1 ≤ f) : p ≤ familyVertices k p f := by
  have hpow : p ≤ p ^ k := by
    calc
      p = p ^ 1 := by simp
      _ ≤ p ^ k := Nat.pow_le_pow_right hp hk
  have hfactor : 1 ≤ 2 * f := by omega
  exact hpow.trans (by simpa [familyVertices] using Nat.mul_le_mul_right (p ^ k) hfactor)

/-- Complete graphs give the repaired k=1 lower bound with explicit constant 1/4. -/
theorem complete_graph_quadratic_lower_bound (n : ℕ) (hn : 2 ≤ n) :
    n ^ 2 ≤ 4 * n.choose 2 := by
  have aux : ∀ m : ℕ, (m + 2) ^ 2 ≤ 4 * (m + 2).choose 2 := by
    intro m
    induction m with
    | zero => norm_num
    | succ m ih =>
      have hchoose : (m + 3).choose 2 = (m + 2) + (m + 2).choose 2 := by
        simpa only [Nat.choose_one_right] using
          (Nat.choose_succ_succ (m + 2) 1)
      rw [show m + 1 + 2 = m + 3 by omega, hchoose]
      nlinarith
  have h := aux (n - 2)
  simpa only [Nat.sub_add_cancel hn] using h

end DegreeFaultSpanners
