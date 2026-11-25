import DirectedFlowCutGap.BinaryNaturalOperations
import DirectedFlowCutGap.BinaryBoundedSampler
import DirectedFlowCutGap.FairBitConfidence

/-! Use the charged binary operations to compute the rejection cap
from the draw bound and the supplied sample count and confidence. -/
namespace DirectedFlowCutGap.MeasuredTapeTrials

open BinaryNaturalOperations (add mul width size_le_self)

def prepare (draw extra confidence : ℕ) : ℕ × ℕ :=
  let count := add extra 1
  let calls := mul count.1 draw
  let digits := width calls.1
  let result := add (max 1 digits.1) confidence
  (result.1,count.2+calls.2+digits.2+result.2+16*(digits.1+1)+12)

private theorem width_eq (n : ℕ) : max 1 n.size = FairBitWords.width n := by
  by_cases h : 0 < n
  · rw [BinaryBoundedSampler.size_eq_width h,max_eq_right]
    exact FairBitWords.width_pos n
  · have zero : n = 0 := by omega
    subst n
    decide

theorem prepare_value (draw extra confidence : ℕ) :
    (prepare draw extra confidence).1 = FairBitConfidence.trials ((extra+1)*draw) confidence := by
  simp only [prepare,BinaryNaturalOperations.add_value,BinaryNaturalOperations.mul_value,
    BinaryNaturalOperations.width_value,width_eq,FairBitConfidence.trials]

def work (draw extra confidence : ℕ) : ℕ :=
  let B := (extra+1)*(draw+1)+confidence+1
  3*(BinaryRawRational.budget B+4)+(24*(B+1)^2+4)+16*(B+1)+12

theorem prepare_charge (draw extra confidence : ℕ) :
    (prepare draw extra confidence).2 ≤ work draw extra confidence := by
  let span := (extra+1)*(draw+1)
  let B := span+confidence+1
  let count := add extra 1
  let calls := mul count.1 draw
  let digits := width calls.1
  let cap := add (max 1 digits.1) confidence
  have count_span : extra+1 ≤ span := by
    simpa only [span,Nat.mul_one] using Nat.mul_le_mul_left (extra+1) (show 1 ≤ draw+1 by omega)
  have draw_span : draw+1 ≤ span := by
    simpa only [span,Nat.one_mul] using Nat.mul_le_mul_right (draw+1) (show 1 ≤ extra+1 by omega)
  have input {x : ℕ} (le : x ≤ span) : x.size ≤ B :=
    (size_le_self x).trans (le.trans (by omega))
  have countSize : count.1.size ≤ B := by
    rw [show count.1 = extra+1 from BinaryNaturalOperations.add_value ..]
    exact input count_span
  have callSize : calls.1.size ≤ B := by
    rw [show calls.1 = (extra+1)*draw by simp only [calls,count,BinaryNaturalOperations.mul_value,
      BinaryNaturalOperations.add_value]]
    exact input (Nat.mul_le_mul_left _ (Nat.le_succ _))
  have digitsBound : digits.1 ≤ B := (BinaryNaturalOperations.width_value _).trans_le callSize
  have first : count.2 ≤ BinaryRawRational.budget B+4 :=
    BinaryNaturalOperations.add_paid (input (by omega)) (input (by omega))
  have second : calls.2 ≤ BinaryRawRational.budget B+4 :=
    BinaryNaturalOperations.mul_paid countSize (input (by omega))
  have third : digits.2 ≤ 24*(B+1)^2+4 := BinaryNaturalOperations.width_paid callSize
  have fourth : cap.2 ≤ BinaryRawRational.budget B+4 := BinaryNaturalOperations.add_paid
    ((size_le_self _).trans (max_le (by omega) digitsBound))
    ((size_le_self confidence).trans (by omega))
  change count.2+calls.2+digits.2+cap.2+16*(digits.1+1)+12 ≤
    3*(BinaryRawRational.budget B+4)+(24*(B+1)^2+4)+16*(B+1)+12
  omega

end DirectedFlowCutGap.MeasuredTapeTrials
