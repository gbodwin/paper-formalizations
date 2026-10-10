import GreedyShortcuts.WeightedBenchmark

/-! Parameter monotonicity and explicit logarithmic comparison-budget rounding. -/
namespace GreedyShortcuts.WeightedBenchmark

open DirectedPaths WeightedPaths WeightedGreedy
open scoped NNReal
universe u
variable {V U : Type u} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]

theorem exopt_mono_parameters (hn : Fintype.card V ≤ Fintype.card U)
    {m M h H : ℕ} (hm : m ≤ M) (hh : H ≤ h) : exopt V m h ≤ exopt U M H := by
  apply exopt_le
  intro W _ _ hW G w hG
  obtain ⟨J,hJ,hc,hb⟩ := (exopt_spec (V := U) M H) W (hW.trans hn) G w (hG.trans hm)
  exact ⟨J,hJ,hc.trans hh,hb⟩

theorem exopt_card_congr (hn : Fintype.card V = Fintype.card U) (m h : ℕ) :
    exopt V m h = exopt U m h := by
  exact le_antisymm (exopt_mono_parameters hn.le le_rfl le_rfl)
    (exopt_mono_parameters hn.ge le_rfl le_rfl)

theorem log_cube_bound (n : ℕ) (hn : 2 ≤ n) :
    Nat.log 2 (n^3) + 1 ≤ 6 * Nat.log 2 n := by
  have hp : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by decide) n
  have hcube : n^3 < 2 ^ (3*(Nat.log 2 n + 1)) := by
    have h := Nat.pow_lt_pow_left hp (by decide : 3 ≠ 0)
    simpa [← pow_mul, Nat.mul_comm] using h
  have hl := Nat.log_lt_of_lt_pow (show n^3 ≠ 0 by positivity) hcube
  have hone : 1 ≤ Nat.log 2 n := (Nat.le_log_iff_pow_le (by decide) (by omega)).mpr (by simpa using hn)
  omega

/-- A simple sufficient budget with a visible absolute constant. -/
theorem logarithmic_budget_fits (n m : ℕ) (hn : 2 ≤ n) :
    (Nat.log 2 (n^3) + 1) * (2 * (m / (12 * Nat.log 2 n))) ≤ m := by
  have hk := log_cube_bound n hn
  have hdiv := Nat.div_mul_le_self m (12 * Nat.log 2 n)
  have hmul := Nat.mul_le_mul_right (m / (12 * Nat.log 2 n)) hk
  nlinarith

/-- The asymptotic logarithmic parameter can be instantiated with an exact
natural-number floor, without changing the greedy graph model. -/
theorem directed_logarithmic_budget (G : V → V → Prop) (w : V → V → ℝ≥0)
    (m : ℕ) (hG : (edges G).card ≤ m) (hn : 2 ≤ Fintype.card V) :
    let h := m / (12 * Nat.log 2 (Fintype.card V))
    let β := max 1 (2 * exopt V (2*m) h)
    (output G w β (Nat.le_max_left _ _)).card ≤ m := by
  dsimp only
  exact output_card_of_universal_bound G w m _ _ _ hG (Nat.le_max_left _ _)
    (Nat.le_max_right _ _) (exopt_spec _ _) (logarithmic_budget_fits _ _ hn)

end GreedyShortcuts.WeightedBenchmark
