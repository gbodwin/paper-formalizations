import DirectedFlowCutGap.DyadicEdgeWeights
import DirectedFlowCutGap.RawNonnegativeRational

/-!
# Stored rational dyadic labels for edge rounding

The cutoffs and dyadic comparisons operate on numerator and denominator
fields. The returned finite label agrees with the real-valued dyadic
preparation, including zero, small weights, and weights at least one.
-/

namespace DirectedFlowCutGap.EncodedEdgeLabels

open scoped NNReal
open RawNonnegativeRational

def dyadicCode (k : ℕ) : Code := Code.one.div (Code.ofNat (2 ^ k))

theorem dyadicCode_value (k : ℕ) :
    (dyadicCode k).realValue = DyadicEdgeWeights.dyadic k := by
  rw [DyadicEdgeWeights.dyadic_eq_one_div]
  simp [dyadicCode, Code.realValue, Code.value_div, Code.value_one, Code.value_ofNat]

theorem dyadicCode_bounded (k : ℕ) : (dyadicCode k).Bounded k := by
  have h : (Code.ofNat (2 ^ k)).Bounded k := by
    exact ⟨le_rfl, Nat.one_le_two_pow⟩
  simpa only [dyadicCode, Nat.zero_add] using Code.bounded_div Code.bounded_one h

def cutoffCode (n : ℕ) : Code := Code.one.div (Code.ofNat (2 * n))

theorem cutoffCode_value (n : ℕ) :
    (cutoffCode n).realValue = DyadicEdgeWeights.cutoff n := by
  simp [cutoffCode, DyadicEdgeWeights.cutoff, Code.realValue, Code.value_div, Code.value_one,
    Code.value_ofNat]

theorem le_real_iff (a b : Code) : a.le b = true ↔ a.realValue ≤ b.realValue := by
  rw [Code.le_eq_true, Code.realValue, Code.realValue, NNRat.cast_le]

def ceilIndex (w : Code) : ℕ → ℕ
  | 0 => 0
  | k + 1 => if w.le (dyadicCode (k + 1)) then k + 1 else ceilIndex w k

theorem ceilIndex_value (w : Code) (k : ℕ) :
    ceilIndex w k = DyadicEdgeWeights.ceilIndex k w.realValue := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [ceilIndex, DyadicEdgeWeights.ceilIndex, le_real_iff, dyadicCode_value, ih]

def label (n : ℕ) (w : Code) : DyadicEdgeWeights.Label n :=
  if n = 0 then none else
  if w.le (cutoffCode n) then none else
  if Code.one.le w then DyadicEdgeWeights.oneLabel n else
    some ⟨ceilIndex w (DyadicEdgeWeights.depth n),
      Nat.lt_succ_of_le (by rw [ceilIndex_value]; exact DyadicEdgeWeights.ceilIndex_le _ _)⟩

theorem label_value (n : ℕ) (w : Code) :
    label n w = DyadicEdgeWeights.round n w.realValue := by
  have hOne : Code.one.realValue = 1 := by simp [Code.realValue]
  simp only [label, DyadicEdgeWeights.round, le_real_iff, cutoffCode_value, hOne, ceilIndex_value]

def valueCode {n : ℕ} : DyadicEdgeWeights.Label n → Code
  | none => Code.zero
  | some k => dyadicCode k.val

theorem valueCode_value {n : ℕ} (i : DyadicEdgeWeights.Label n) :
    (valueCode i).realValue = DyadicEdgeWeights.value n i := by
  cases i with
  | none => simp [valueCode, Code.realValue]
  | some k => exact dyadicCode_value k.val

theorem valueCode_bounded {n : ℕ} (i : DyadicEdgeWeights.Label n) :
    (valueCode i).Bounded (DyadicEdgeWeights.depth n) := by
  cases i with
  | none => exact Code.bounded_mono Code.bounded_zero (Nat.zero_le _)
  | some k => exact Code.bounded_mono (dyadicCode_bounded k.val) (Nat.le_of_lt_succ k.isLt)

end DirectedFlowCutGap.EncodedEdgeLabels
