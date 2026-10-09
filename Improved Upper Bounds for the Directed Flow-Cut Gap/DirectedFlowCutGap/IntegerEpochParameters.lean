import DirectedFlowCutGap.CandidateSchedule
import DirectedFlowCutGap.SubpolynomialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Integer parameters for a finite implementation

Restart tests can use the natural number `log2 (n+2)+2`. A natural-logarithm
calculation proves its analytical bounds, but the parameter itself uses only
integer arithmetic. Its exact restart fuel and cap envelope are also natural
numbers. These lemmas do not assert that the existing choice-based schedule
already uses this replacement or that its full implementation is polynomial.
-/
namespace DirectedFlowCutGap.IntegerEpochParameters
open scoped BigOperators NNReal ENNReal
open SubpolynomialBounds

def restart (n : ℕ) : ℕ := Nat.log2 (n + 2) + 2
def fuel (n : ℕ) : ℕ := Nat.log (restart n) (n ^ 3) + 1
def cap (n : ℕ) : ℕ := 4 ^ fuel n

theorem two_le_restart (n : ℕ) : 2 ≤ restart n := by
  unfold restart
  omega

theorem one_lt_restart (n : ℕ) : 1 < restart n := by
  have := two_le_restart n
  omega

theorem log_size_le_restart (n : ℕ) :
    Real.log ((n : ℝ) + 2) ≤ (restart n : ℝ) := by
  have hp : (n : ℝ) + 2 < (2 : ℝ) ^ (Nat.log2 (n + 2) + 1) := by
    exact_mod_cast (show n + 2 < 2 ^ (Nat.log2 (n + 2) + 1) by
      simpa only [Nat.log2_eq_log_two] using Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (n + 2))
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < n + 2) hp.le
  rw [Real.log_pow] at hlog
  have ht : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hh := mul_le_mul_of_nonneg_left ht
    (Nat.cast_nonneg (α := ℝ) (Nat.log2 (n + 2) + 1))
  dsimp [restart]
  push_cast at hlog hh ⊢
  linarith

theorem analytical_restart_le (n : ℕ) : r n ≤ (restart n : ℝ) := by
  unfold r
  exact max_le (by exact_mod_cast two_le_restart n) (log_size_le_restart n)

theorem restart_le_log_envelope (n : ℕ) :
    (restart n : ℝ) ≤ Real.log ((n : ℝ) + 2) / Real.log 2 + 2 := by
  have h := Real.log2_le_logb (n + 2)
  simpa only [restart, Nat.cast_add, Nat.cast_ofNat, Real.logb, add_comm] using add_le_add_right h 2

theorem restart_subpolynomial : Subpolynomial (fun n => (restart n : ℝ)) := by
  apply (((Subpolynomial.const (1 / Real.log 2)).mul log_size_subpolynomial).add
    (Subpolynomial.const 2)).mono
  intro n _
  have hlogtwo := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hlog := (log_size_pos n).le
  rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (by positivity)]
  simpa only [div_eq_mul_inv, mul_comm, one_mul] using restart_le_log_envelope n

theorem cubic_lt_restart_power (n : ℕ) : n ^ 3 < restart n ^ fuel n := by
  exact Nat.lt_pow_succ_log_self (one_lt_restart n) _

theorem fuel_le_analytical (n : ℕ) : fuel n ≤ J n + 1 := by
  by_cases hn : n = 0
  · simp [fuel, hn]
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hp : (restart n : ℝ) ^ Nat.log (restart n) (n ^ 3) ≤ (n : ℝ) ^ (3 : ℕ) := by
      exact_mod_cast Nat.pow_log_le_self (restart n) (pow_ne_zero 3 hn)
    have hr : r n ^ Nat.log (restart n) (n ^ 3) ≤ (n : ℝ) ^ (3 : ℕ) :=
      (pow_le_pow_left₀ (r_pos n).le (analytical_restart_le n) _).trans hp
    exact Nat.succ_le_succ (restart_count_le_J hn1 hr)

theorem cap_le_analytical (n : ℕ) : (cap n : ℝ) ≤ 4 * B n := by
  have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) (fuel_le_analytical n)
  simpa [cap, B, pow_succ, mul_comm] using hp

theorem cap_subpolynomial : Subpolynomial (fun n => (cap n : ℝ)) := by
  apply ((Subpolynomial.const 4).mul B_subpolynomial).mono
  intro n _
  rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_pos (mul_pos (by norm_num) (B_pos n))]
  exact cap_le_analytical n

theorem fuel_add_one_subpolynomial : Subpolynomial (fun n => (fuel n : ℝ) + 1) := by
  apply (J_add_one_subpolynomial.add (Subpolynomial.const 1)).mono
  intro n _
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  have h : (fuel n : ℝ) ≤ (J n : ℝ) + 1 := by exact_mod_cast fuel_le_analytical n
  linarith

/-- A coarse explicit polynomial bounds the integer cap, without asymptotics. -/
theorem cap_le_polynomial {n : ℕ} (hn : 1 ≤ n) : cap n ≤ 4 * n ^ 6 := by
  have hn0 : n ≠ 0 := by omega
  have hp := Nat.pow_log_le_self (restart n) (pow_ne_zero 3 hn0)
  have htwo : 2 ^ Nat.log (restart n) (n ^ 3) ≤ n ^ 3 :=
    (Nat.pow_le_pow_left (two_le_restart n) _).trans hp
  have hs := Nat.pow_le_pow_left htwo 2
  have he : (2 ^ Nat.log (restart n) (n ^ 3)) ^ 2 =
      4 ^ Nat.log (restart n) (n ^ 3) := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  rw [he, ← pow_mul] at hs
  change 4 ^ (Nat.log (restart n) (n ^ 3) + 1) ≤ _
  rw [pow_succ, mul_comm]
  exact Nat.mul_le_mul_left 4 (by simpa only [Nat.reduceMul] using hs)

section Threshold
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Unweighted internal path lengths are integers, so ceiling the threshold is exact. -/
theorem unweightedDemands_ceil (G : Digraph V) (L : ℝ≥0) :
    CandidateSchedule.unweightedDemands G (Nat.ceil (L : ℝ) : ℝ≥0) =
      CandidateSchedule.unweightedDemands G L := by
  ext p
  simp only [CandidateSchedule.unweightedDemands, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [coe_le_vertexDistance_iff, coe_le_vertexDistance_iff]
  constructor
  · intro h path
    have hp := h path
    rw [SimplePath.weight_unit] at hp ⊢
    have hc : L ≤ (Nat.ceil (L : ℝ) : ℝ≥0) := by exact_mod_cast Nat.le_ceil (L : ℝ)
    exact hc.trans hp
  · intro h path
    have hp := h path
    rw [SimplePath.weight_unit] at hp ⊢
    have hr : (L : ℝ) ≤ (path.internalVertices.card : ℝ) := by exact_mod_cast hp
    exact_mod_cast (Nat.ceil_le.mpr hr)

end Threshold
end DirectedFlowCutGap.IntegerEpochParameters
