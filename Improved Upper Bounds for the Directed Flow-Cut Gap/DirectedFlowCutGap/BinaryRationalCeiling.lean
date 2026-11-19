import DirectedFlowCutGap.BinaryRational
import DirectedFlowCutGap.BinaryDivision

/-! Ceiling by Boolean-list addition, predecessor and long division. -/

namespace DirectedFlowCutGap.BinaryRationalCeiling

open BinaryArithmetic BinaryRational RawNonnegativeRational

def ceil (q : Fraction) : Bits × ℕ :=
  let total := addCanonical q.num q.den
  let prior := predecessor total.1
  let quotient := BinaryDivision.divide prior.1 q.den
  (quotient.quotient,total.2+prior.2+quotient.steps+8)

theorem ceil_value (q : Fraction) : value (ceil q).1=(decode q).ceil := by
  simp only [ceil,(BinaryDivision.divide_spec ..).1,(predecessor_spec _).1,(canonical_values ..).1,
    Code.ceil,decode]

theorem ceil_width (q : Fraction) : (ceil q).1.length=(decode q).ceil.size := by
  rw [← ceil_value]
  unfold ceil
  simp only [(BinaryDivision.divide_spec ..).1,(BinaryDivision.divide_spec ..).2.2.1]

def budget (B : ℕ) : ℕ := 4096*(B+2)^2

theorem ceil_paid {q : Fraction} {B : ℕ} (fits : StoredBounded q B) : (ceil q).2 ≤ budget B := by
  let total := addCanonical q.num q.den
  let prior := predecessor total.1
  let d := BinaryDivision.divide prior.1 q.den
  have i := fits.1
  have j := fits.2
  have addPaid : total.2 ≤ 32*(B+2) := (canonical_charges i j).1
  have too : value q.num+value q.den<2^(B+1) := by
    rw [Nat.pow_succ]
    have p := (value_lt q.num).trans_le (Nat.pow_le_pow_right (by decide) i)
    have r := (value_lt q.den).trans_le (Nat.pow_le_pow_right (by decide) j)
    omega
  have totalWidth : total.1.length≤B+1 := by
    change (addCanonical q.num q.den).1.length ≤ B+1
    rw [(canonical_values q.num q.den).2.2.1]
    exact Nat.size_le.mpr too
  have previous := predecessor_spec total.1
  have priorWidth : prior.1.length≤B+1 := by
    have s : (value total.1-1).size ≤ (value total.1).size := Nat.size_le_size (Nat.sub_le _ _)
    have wt := Nat.size_le.mpr (value_lt total.1)
    calc
      prior.1.length = (value total.1-1).size := previous.2.1
      _ ≤ _ := s.trans (wt.trans totalWidth)
  have priorPaid : prior.2 ≤ 32*(B+2) := previous.2.2.trans (by omega)
  have divPaid : d.steps ≤ 1024*(B+2)^2 :=
    BinaryDivision.divide_charge_bound priorWidth (j.trans (Nat.le_succ B))
  change total.2+prior.2+d.steps+8 ≤ budget B
  unfold budget
  nlinarith

def ofCode (q : Code) : Fraction := ⟨q.num.bits,q.den.bits,by rw [value_bits]; exact q.positive_den⟩

@[simp] theorem decode_ofCode (q : Code) : decode (ofCode q)=q := by
  cases q
  simp [decode,ofCode,value_bits]

theorem code_width {q : Code} {B : ℕ} (fits : q.Bounded B) : StoredBounded (ofCode q) (B+1) := by
  change q.num.bits.length ≤ B+1 ∧ q.den.bits.length ≤ B+1
  simpa only [Nat.size_eq_bits_len] using Code.bounded_bits fits

end DirectedFlowCutGap.BinaryRationalCeiling
