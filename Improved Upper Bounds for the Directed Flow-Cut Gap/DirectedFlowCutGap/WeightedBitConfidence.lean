import DirectedFlowCutGap.WeightedFailureBudget
import DirectedFlowCutGap.FairBitConfidence
import DirectedFlowCutGap.BinaryArithmetic

/-!
# An actual binary trial word for the original-weight failure tolerance

The encoded inputs are a bound on the number of rejection-sampler calls, the
number of original resources, and the maximum supplied numerator/denominator
width. Three Boolean-list additions construct `Q + 2*B + m + 2` trials.
This deliberately coarse polynomial budget avoids an executable logarithm,
an encoded approximation factor, and any normalization of the original weights.

The probability lemma prices all `Q` bounded-rejection failures together at
half the tolerance from `WeightedFailureBudget`. The caller still has to prove
the actual adaptive call bound and its probability-transfer theorem. A second
half can pay oracle-cost failure; that claim is not supplied by this module.
-/
namespace DirectedFlowCutGap.WeightedBitConfidence

open BinaryArithmetic

/-- Conservative numerical trial budget, polynomial in its three parameters. -/
def trialCount (Q m B : ℕ) : ℕ := Q + 2*B + m + 2

/-- Only Boolean-list addition computes the output. Natural values and the
charge accumulator are proof/instrumentation fields, not executable operands. -/
def prepare (calls resources width : Bits) : Bits × ℕ :=
  let a := BinaryArithmetic.add false calls (false :: width)
  let b := BinaryArithmetic.add false a.1 resources
  let c := BinaryArithmetic.add false b.1 [false, true]
  (c.1, a.2 + b.2 + c.2 + 12)

theorem prepare_value (calls resources width : Bits) :
    value (prepare calls resources width).1 =
      trialCount (value calls) (value resources) (value width) := by
  have ha := (add_spec false calls (false :: width)).1
  have hb := (add_spec false (add false calls (false :: width)).1 resources).1
  have hc := (add_spec false
    (add false (add false calls (false :: width)).1 resources).1 [false, true]).1
  simp only [value, Bool.toNat_false, Bool.toNat_true] at ha hb hc
  simp only [prepare, trialCount]
  omega

/-- Supplied padding is included. The result is not assumed canonical. -/
theorem prepare_length (calls resources width : Bits) (K : ℕ)
    (hc : calls.length ≤ K) (hm : resources.length ≤ K) (hB : width.length ≤ K) :
    (prepare calls resources width).1.length ≤ K + 4 := by
  have ha := (add_spec false calls (false :: width)).2.1
  have hb := (add_spec false (add false calls (false :: width)).1 resources).2.1
  have hd := (add_spec false
    (add false (add false calls (false :: width)).1 resources).1 [false, true]).2.1
  simp only [List.length_cons, List.length_nil] at ha hb hd
  simp only [prepare]
  omega

theorem prepare_charge (calls resources width : Bits) (K : ℕ)
    (hc : calls.length ≤ K) (hm : resources.length ≤ K) (hB : width.length ≤ K) :
    (prepare calls resources width).2 ≤ 64*(K+4) := by
  have ha := add_spec false calls (false :: width)
  have hb := add_spec false (add false calls (false :: width)).1 resources
  have hd := add_spec false
    (add false (add false calls (false :: width)).1 resources).1 [false, true]
  simp only [List.length_cons, List.length_nil] at ha hb hd
  simp only [prepare]
  omega

theorem trialCount_ge_confidence (Q m B : ℕ) :
    FairBitConfidence.trials Q (WeightedFailureBudget.exponent m B + 1) ≤
      trialCount Q m B := by
  have hQ := FairBitConfidence.trials_le Q (WeightedFailureBudget.exponent m B + 1)
  have hE := WeightedFailureBudget.exponent_bound m B
  unfold trialCount
  omega

theorem accumulated_failure (Q m B : ℕ) :
    (Q : ℝ) * ((1 : ℝ)/2)^(trialCount Q m B) ≤
      WeightedFailureBudget.tolerance m B / 2 := by
  have hpow : ((1 : ℝ)/2)^(trialCount Q m B) ≤
      ((1 : ℝ)/2)^(FairBitConfidence.trials Q
        (WeightedFailureBudget.exponent m B + 1)) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (trialCount_ge_confidence Q m B)
  have h := (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg Q)).trans
    (FairBitConfidence.accumulated_failure Q (WeightedFailureBudget.exponent m B + 1))
  have he : ((1 : ℝ)/2)^(WeightedFailureBudget.exponent m B + 1) =
      WeightedFailureBudget.tolerance m B / 2 := by
    rw [pow_succ, div_pow, one_pow]
    simp only [WeightedFailureBudget.tolerance, div_eq_mul_inv, one_mul]
  exact h.trans_eq he

/-- The actual computed word supplies the preceding numerical guarantee. -/
theorem prepared_failure (calls resources width : Bits) :
    (value calls : ℝ) * ((1 : ℝ)/2)^(value (prepare calls resources width).1) ≤
      WeightedFailureBudget.tolerance (value resources) (value width) / 2 := by
  rw [prepare_value]
  exact accumulated_failure _ _ _

/-- This arithmetic split is usable after separate adaptive error proofs for
the oracle calls and the bounded ticket sampler have been established. -/
theorem split_error {m B : ℕ} {oracleError samplerError : ℝ}
    (ho : oracleError ≤ WeightedFailureBudget.tolerance m B / 2)
    (hs : samplerError ≤ WeightedFailureBudget.tolerance m B / 2) :
    oracleError + samplerError ≤ WeightedFailureBudget.tolerance m B := by
  linarith

end DirectedFlowCutGap.WeightedBitConfidence
