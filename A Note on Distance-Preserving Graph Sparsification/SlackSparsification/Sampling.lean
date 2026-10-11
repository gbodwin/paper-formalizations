import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-! A finite weighted expectation argument selecting a single sample with
both constant coverage and bounded cost. No independence is required here. -/
namespace SlackSparsification
open Finset
open scoped BigOperators

/-- If the expected coverage is at least `β * p` and the expected cost is at
most `C`, one outcome covers at least `β * p / 2` at cost at most `2*C/β`.
The positive-budget case suffices for all nonempty graph applications. -/
theorem exists_joint_sample {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (w X Y : Ω → ℝ) (p β C : ℝ)
    (hw : ∀ ω, 0 ≤ w ω) (hw1 : ∑ ω, w ω = 1)
    (hX : ∀ ω, X ω ≤ p) (hY : ∀ ω, 0 ≤ Y ω)
    (hp : 0 < p) (hβ : 0 < β) (hC : 0 < C)
    (hEX : β * p ≤ ∑ ω, w ω * X ω)
    (hEY : ∑ ω, w ω * Y ω ≤ C) :
    ∃ ω, β * p / 2 ≤ X ω ∧ Y ω ≤ 2 * C / β := by
  classical
  let score := fun ω => 2 * C * X ω - β * p * Y ω
  obtain ⟨ω, _, hmax⟩ := exists_max_image univ score univ_nonempty
  have havg : (∑ u, w u * score u) ≤ score ω := by
    calc
      _ ≤ ∑ u, w u * score ω := sum_le_sum fun u _ =>
        mul_le_mul_of_nonneg_left (hmax u (mem_univ u)) (hw u)
      _ = score ω := by rw [← sum_mul, hw1, one_mul]
  have hexpand : (∑ u, w u * score u) =
      2 * C * (∑ u, w u * X u) - β * p * (∑ u, w u * Y u) := by
    simp only [score, mul_sub, sum_sub_distrib, mul_sum]
    congr 1 <;> apply sum_congr rfl <;> intro i hi <;> ring
  have hex : C * (β * p) ≤ score ω := by
    rw [hexpand] at havg
    have hx := mul_le_mul_of_nonneg_left hEX (show 0 ≤ 2 * C by positivity)
    have hy := mul_le_mul_of_nonneg_left hEY (show 0 ≤ β * p by positivity)
    nlinarith
  have hy0 := hY ω
  have hxmax := hX ω
  change C * (β * p) ≤ 2 * C * X ω - β * p * Y ω at hex
  refine ⟨ω, ?_, ?_⟩
  · have hprod : 0 ≤ β * p * Y ω := by positivity
    nlinarith
  · apply (le_div_iff₀ hβ).mpr
    nlinarith [mul_nonneg hC.le (mul_pos hβ hp).le]

/-- The joint event can cost a constant factor; separate expectation bounds
are deliberately not mistaken for pointwise guarantees. -/
theorem two_outcome_warning :
    ((0 : ℝ) + 2) / 2 = 1 ∧ ((0 : ℝ) + 2) / 2 = 1 ∧
    ¬ ∃ x ∈ ({(0 : ℝ), 2} : Finset ℝ), 1 ≤ x ∧ x ≤ 1 := by
  norm_num

end SlackSparsification
