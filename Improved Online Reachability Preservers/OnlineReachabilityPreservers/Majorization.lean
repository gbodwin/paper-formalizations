import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic

/-! Lemma 29. Prefix domination controls the second moment of sorted lengths. -/

namespace OnlineReachabilityPreservers

open Finset

/-- Weak majorization implies the square-sum inequality. The dominating sequence
can be in its given order, and no assumption on the signs of its entries is needed. -/
theorem lemma29_square_sum (n : ℕ) (a b : ℕ → ℝ)
    (nonneg : ∀ i < n, 0 ≤ a i)
    (decreasing : ∀ i j, i ≤ j → j < n → a j ≤ a i)
    (prefixBounds : ∀ k ≤ n, (∑ i ∈ range k, a i) ≤ ∑ i ∈ range k, b i) :
    (∑ i ∈ range n, (a i) ^ 2) ≤ ∑ i ∈ range n, (b i) ^ 2 := by
  let gap (k : ℕ) : ℝ := ∑ i ∈ range k, (b i - a i)
  let weighted (k : ℕ) : ℝ := ∑ i ∈ range k, a i * (b i - a i)
  have hg (k : ℕ) (hk : k ≤ n) : 0 ≤ gap k := by
    unfold gap
    rw [sum_sub_distrib]
    exact sub_nonneg.mpr (prefixBounds k hk)
  have hw (k : ℕ) (hk : k < n) : a k * gap (k + 1) ≤ weighted (k + 1) := by
    induction k with
    | zero => simp [gap, weighted]
    | succ k ih =>
      have h := mul_le_mul_of_nonneg_right (decreasing k (k + 1) (by omega) hk)
        (hg (k + 1) hk.le)
      have hi := ih (by omega)
      have hgstep : gap (k + 1 + 1) = gap (k + 1) + (b (k + 1) - a (k + 1)) :=
        sum_range_succ (fun i => b i - a i) (k + 1)
      have hwstep : weighted (k + 1 + 1) =
          weighted (k + 1) + a (k + 1) * (b (k + 1) - a (k + 1)) :=
        sum_range_succ (fun i => a i * (b i - a i)) (k + 1)
      rw [hgstep, hwstep, mul_add]
      exact add_le_add (h.trans hi) le_rfl
  have nonnegative : 0 ≤ weighted n := by
    cases n with
    | zero => simp [weighted]
    | succ j =>
      exact (mul_nonneg (nonneg j (by omega)) (hg (j + 1) le_rfl)).trans (hw j (by omega))
  have pointwise : (∑ i ∈ range n, ((a i)^2 + 2 * (a i * (b i - a i)))) ≤
      ∑ i ∈ range n, (b i)^2 := by
    apply sum_le_sum
    intro i _
    nlinarith only [sq_nonneg (a i - b i)]
  rw [sum_add_distrib, ← mul_sum] at pointwise
  change (∑ i ∈ range n, (a i)^2) + 2 * weighted n ≤ _ at pointwise
  linarith

end OnlineReachabilityPreservers
