import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

example (n : ℕ) : n + 0 = n := by omega
example (x : ℝ) : x ^ 2 ≥ 0 := by positivity
#check Real.rpow_mul
