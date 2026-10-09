import DirectedFlowCutGap.IntegerClosureAsymptotic
import Mathlib.Data.Nat.Sqrt

/-!
# Integer cut-cost thresholds

The cutoff used to recognize a successful hard-regime run uses only integer
arithmetic. Its factor is within two of the analytical `(n/L)^(3/2)` scale.
These are exact numerical/probability bridges, not an operation-cost theorem
for division or square root and not a whole-program execution theorem.
-/
namespace DirectedFlowCutGap.IntegerCostThreshold
open scoped NNReal ENNReal
open IntegerClosureAsymptotic EpochParameterBridge FiniteAmplification AdaptiveCost

def factor (n L : ℕ) : ℕ := Nat.sqrt (n ^ 3 / L ^ 3) + 1

theorem factor_pos (n L : ℕ) : 0 < factor n L := by
  unfold factor
  omega

theorem factor_lower_square (n L : ℕ) (hL : 0 < L) :
    n ^ 3 < L ^ 3 * factor n L ^ 2 := by
  have hp : 0 < L ^ 3 := pow_pos hL _
  have hq := Nat.lt_succ_sqrt' (n ^ 3 / L ^ 3)
  have hh := (Nat.div_lt_iff_lt_mul hp).mp hq
  simpa only [factor, Nat.succ_eq_add_one, Nat.mul_comm] using hh

theorem factor_upper_square (n L : ℕ) :
    L ^ 3 * (Nat.sqrt (n ^ 3 / L ^ 3)) ^ 2 ≤ n ^ 3 := by
  exact (Nat.mul_le_mul_left (L ^ 3) (Nat.sqrt_le' _)).trans
    (by simpa only [Nat.mul_comm] using Nat.div_mul_le_self (n ^ 3) (L ^ 3))

theorem factor_le_polynomial (n L : ℕ) : factor n L ≤ n ^ 3 + 1 := by
  exact Nat.add_le_add_right ((Nat.sqrt_le_self _).trans (Nat.div_le_self _ _)) _

variable {V : Type*} [Fintype V]

theorem sizeFactor_square (L : ℕ) :
    (sizeFactor V (L : ℝ≥0)) ^ (2 : ℕ) =
      (Fintype.card V : ℝ) ^ (3 : ℕ) / (L : ℝ) ^ (3 : ℕ) := by
  unfold sizeFactor
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num [div_pow]

theorem sizeFactor_le_factor (L : ℕ) (hL : 0 < L) :
    sizeFactor V (L : ℝ≥0) ≤ (factor (Fintype.card V) L : ℝ) := by
  have hp : (0 : ℝ) < (L : ℝ) ^ (3 : ℕ) := by positivity
  have hs := sizeFactor_square (V := V) L
  have hnat := factor_lower_square (Fintype.card V) L hL
  have hr : (Fintype.card V : ℝ) ^ (3 : ℕ) <
      (L : ℝ) ^ (3 : ℕ) * (factor (Fintype.card V) L : ℝ) ^ (2 : ℕ) := by
    exact_mod_cast hnat
  have hd : (Fintype.card V : ℝ) ^ (3 : ℕ) / (L : ℝ) ^ (3 : ℕ) <
      (factor (Fintype.card V) L : ℝ) ^ (2 : ℕ) :=
    (div_lt_iff₀ hp).mpr (by simpa only [mul_comm] using hr)
  rw [← hs] at hd
  have hf := Nat.cast_nonneg (α := ℝ) (factor (Fintype.card V) L)
  nlinarith

theorem factor_le_sizeFactor_add_one (L : ℕ) (hL : 0 < L) :
    (factor (Fintype.card V) L : ℝ) ≤ sizeFactor V (L : ℝ≥0) + 1 := by
  have hp : (0 : ℝ) < (L : ℝ) ^ (3 : ℕ) := by positivity
  have hs := sizeFactor_square (V := V) L
  have hnat := factor_upper_square (Fintype.card V) L
  have hr : (L : ℝ) ^ (3 : ℕ) *
      (Nat.sqrt (Fintype.card V ^ 3 / L ^ 3) : ℝ) ^ (2 : ℕ) ≤
      (Fintype.card V : ℝ) ^ (3 : ℕ) := by exact_mod_cast hnat
  have hd : (Nat.sqrt (Fintype.card V ^ 3 / L ^ 3) : ℝ) ^ (2 : ℕ) ≤
      (Fintype.card V : ℝ) ^ (3 : ℕ) / (L : ℝ) ^ (3 : ℕ) :=
    (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using hr)
  rw [← hs] at hd
  have hsf : 0 ≤ sizeFactor V (L : ℝ≥0) := Real.rpow_nonneg (by positivity) _
  simp only [factor, Nat.cast_add, Nat.cast_one]
  nlinarith

theorem factor_le_twice_sizeFactor (L : ℕ) (hL : 0 < L) (hLn : L ≤ Fintype.card V) :
    (factor (Fintype.card V) L : ℝ) ≤ 2 * sizeFactor V (L : ℝ≥0) := by
  have hf := factor_le_sizeFactor_add_one (V := V) L hL
  have hone := one_le_sizeFactor (V := V) (L := (L : ℝ≥0))
    (by exact_mod_cast hL) (by exact_mod_cast hLn)
  linarith

def cutoff (n L : ℕ) : ℕ := 2 * envelopeCode n * factor n L

theorem envelopeCode_pos (n : ℕ) : 0 < envelopeCode n := by
  unfold envelopeCode
  positivity

theorem cutoff_pos (n L : ℕ) : 0 < cutoff n L := by
  exact Nat.mul_pos (Nat.mul_pos (by decide) (envelopeCode_pos n)) (factor_pos n L)

theorem cutoff_lower (L : ℕ) (hL : 0 < L) :
    2 * (envelope (Fintype.card V) * sizeFactor V (L : ℝ≥0)) ≤
      (cutoff (Fintype.card V) L : ℝ) := by
  have henv : 0 ≤ envelope (Fintype.card V) := by
    rw [← envelopeCode_eq]
    positivity
  have h := mul_le_mul_of_nonneg_left (sizeFactor_le_factor (V := V) L hL)
    (by positivity : 0 ≤ 2 * envelope (Fintype.card V))
  simpa only [cutoff, Nat.cast_mul, Nat.cast_ofNat, envelopeCode_eq, mul_assoc] using h

theorem cutoff_upper (L : ℕ) (hL : 0 < L) (hLn : L ≤ Fintype.card V) :
    (cutoff (Fintype.card V) L : ℝ) ≤
      4 * envelope (Fintype.card V) * sizeFactor V (L : ℝ≥0) := by
  have henv : 0 ≤ envelope (Fintype.card V) := by
    rw [← envelopeCode_eq]
    positivity
  have h := mul_le_mul_of_nonneg_left (factor_le_twice_sizeFactor (V := V) L hL hLn)
    (by positivity : 0 ≤ 2 * envelope (Fintype.card V))
  simpa only [cutoff, Nat.cast_mul, Nat.cast_ofNat, envelopeCode_eq] using
    (show 2 * envelope (Fintype.card V) * (factor (Fintype.card V) L : ℝ) ≤
      4 * envelope (Fintype.card V) * sizeFactor V (L : ℝ≥0) by nlinarith [h])

section Probability
noncomputable section
variable [DecidableEq V]

/-- The integer success check fails with probability at most one half. -/
theorem coreLaw_cutoff_failure (G : Digraph V) [DecidableRel G.Adj]
    (L : ℕ) (hL : 0 < L) (E : NetworkEnumeration V L)
    (hHard : 64 * IntegerEpochParameters.cap (Fintype.card V) ≤ L)
    (hLn : L ≤ Fintype.card V) (hnL : Fintype.card V ≤ L ^ 3) :
    probability (coreLaw G L hL E)
      (fun X => cutoff (Fintype.card V) L < X.card) ≤ (1 : ℝ) / 2 := by
  have hp : (0 : ℝ) < cutoff (Fintype.card V) L := by
    exact_mod_cast cutoff_pos (Fintype.card V) L
  have hm := threshold_mul_probability_le_expectedCost (coreLaw G L hL E)
    (fun X => (X.card : ℝ)) (fun X => Nat.cast_nonneg X.card)
      (cutoff (Fintype.card V) L) hp.le
  have he := coreLaw_expected G L hL E hHard hLn hnL
  have hc := cutoff_lower (V := V) L hL
  have hevent : (fun X : Finset V => (cutoff (Fintype.card V) L : ℝ) < (X.card : ℝ)) =
      (fun X : Finset V => cutoff (Fintype.card V) L < X.card) := by
    funext X
    exact propext Nat.cast_lt
  rw [hevent] at hm
  nlinarith

end
end Probability

end DirectedFlowCutGap.IntegerCostThreshold
