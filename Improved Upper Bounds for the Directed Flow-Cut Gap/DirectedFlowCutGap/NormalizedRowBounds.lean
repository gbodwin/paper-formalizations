import DirectedFlowCutGap.NormalizedRowExecution

namespace DirectedFlowCutGap.NormalizedRow
open BinaryRational
open PackedBooleanConstructor RationalComparisonProgram

def scalarWidth (n B : ℕ) : ℕ := (n+1)*(B+2)+1

theorem alpha_width (xs : List Fraction) (mask : List Bool) (B : ℕ)
    (aligned : xs.length=mask.length) (row : ∀ x∈xs,StoredBounded x B) :
    StoredBounded (alpha xs mask) (scalarWidth xs.length B) := by
  have hm := MaskedRationalRow.result_width xs mask B row
  have hs := BinaryFractionalRows.sum_stored_bound (MaskedRationalRow.result xs mask) (B+1)
    (fun x hx => BinaryFractionalRows.stored_raw_bound (hm x hx))
  rw [MaskedRationalRow.result_length xs mask aligned] at hs
  have hk : xs.length*(B+1+1)+1 ≤ scalarWidth xs.length B := by unfold scalarWidth;nlinarith
  exact ⟨hs.1.trans hk,hs.2.trans hk⟩

def instructionBound (n B : ℕ) : ℕ :=
  17*n+4+CanonicalRationalSum.instructionBound n (B+1)+
    ScalarQuotientRow.instructionBound n (scalarWidth n B)+10

theorem steps_bound (xs : List Fraction) (mask : List Bool) (B : ℕ)
    (aligned : xs.length=mask.length) (row : ∀ x∈xs,StoredBounded x B) :
    steps xs mask ≤ instructionBound xs.length B := by
  have hm := MaskedRationalRow.steps_bound mask
  have hs := CanonicalRationalSum.steps_bound (MaskedRationalRow.result xs mask) (B+1)
    (MaskedRationalRow.result_width xs mask B row)
  rw [MaskedRationalRow.result_length xs mask aligned] at hs
  have hb : B ≤ scalarWidth xs.length B := by unfold scalarWidth;nlinarith
  have hr := ScalarQuotientRow.steps_bound false (alpha xs mask) xs (scalarWidth xs.length B)
    (alpha_width xs mask B aligned row) (fun x hx => ⟨(row x hx).1.trans hb,(row x hx).2.trans hb⟩)
  dsimp [steps,instructionBound]
  omega

/-- Both the length and every quotient field are literally the old output. -/
theorem result_eq_normalized {m : ℕ} (y : BinaryFractionalRows.Row m) (mask : Vector Bool m) :
    result y.toList mask.toList=(BinaryFractionalRows.normalized y mask).1.toList := by
  unfold result alpha
  rw [MaskedRationalRow.sum_result_eq_length]
  exact ScalarQuotientRow.result_eq_normalized y mask
end DirectedFlowCutGap.NormalizedRow
