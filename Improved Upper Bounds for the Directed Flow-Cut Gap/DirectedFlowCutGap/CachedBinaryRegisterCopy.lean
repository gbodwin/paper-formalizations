import DirectedFlowCutGap.CachedScalarRead

/-! Copy the four register words and combine their legacy fees with binary addition. -/
namespace DirectedFlowCutGap.CachedBinaryRegisterCopy

open BinaryArithmetic ImmutableReferenceSimulation EncodedSequenceAccess
open CachedScalarRead (sumMeasured sum_value sum_paid)

def copy (registers : Registers Bits) : (Registers Bits × ℕ) × ℕ :=
  let a := copyBits registers.a
  let b := copyBits registers.b
  let c := copyBits registers.c
  let d := copyBits registers.d
  let fee := sumMeasured [a.2, b.2, c.2, d.2, 4]
  ((⟨a.1, b.1, c.1, d.1⟩, fee.1), fee.2)

theorem value_eq (registers : Registers Bits) : (copy registers).1 = copyRegisters registers := by
  simp only [copy, copyRegisters, sum_value, List.sum_cons, List.sum_nil,
    Nat.add_zero, Nat.add_assoc]

def budget (width : ℕ) : ℕ := 5 * (96 * (width + 2)^2 + 4) + 1

theorem paid {width : ℕ} (registers : Registers Bits) (fits : (copy registers).1.2.size ≤ width) :
    (copy registers).2 ≤ budget width := by
  let fees := [(copyBits registers.a).2, (copyBits registers.b).2,
    (copyBits registers.c).2, (copyBits registers.d).2, 4]
  change (sumMeasured fees).1.size ≤ width at fits
  rw [sum_value] at fits
  exact sum_paid fees fits

end DirectedFlowCutGap.CachedBinaryRegisterCopy
