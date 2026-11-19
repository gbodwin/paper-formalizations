import DirectedFlowCutGap.BinaryNaturalView
import DirectedFlowCutGap.BinaryRationalCeiling

/-! Execute raw rational operations as binary routines and return exactly
the previous numerator and denominator fields, with conversion charges. -/

namespace DirectedFlowCutGap.BinaryRawRational

open BinaryArithmetic BinaryRational RawNonnegativeRational

def encode (q : Code) : Fraction × ℕ :=
  let n := BinaryNaturalView.encode q.num
  let d := BinaryNaturalView.encode q.den
  (⟨n.1,d.1,by rw [BinaryNaturalView.encode_value]; exact q.positive_den⟩,n.2+d.2+8)

theorem encode_eq (q : Code) : (encode q).1=BinaryRationalCeiling.ofCode q := by
  cases q
  simp [encode,BinaryRationalCeiling.ofCode,BinaryNaturalView.encode_bits]

@[simp] theorem encode_value (q : Code) : BinaryRational.decode (encode q).1=q := by
  rw [encode_eq,BinaryRationalCeiling.decode_ofCode]

theorem encode_width {q : Code} {B : ℕ} (fit : q.Bounded B) : StoredBounded (encode q).1 (B+1) := by
  rw [encode_eq]
  exact BinaryRationalCeiling.code_width fit

theorem encode_paid {q : Code} {B : ℕ} (fit : q.Bounded B) : (encode q).2 ≤ 40*(B+2)^2 := by
  have fields := Code.bounded_bits fit
  have a := (BinaryNaturalView.encode_paid q.num).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right fields.1 1) 2))
  have b := (BinaryNaturalView.encode_paid q.den).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right fields.2 1) 2))
  change (BinaryNaturalView.encode q.num).2+(BinaryNaturalView.encode q.den).2+8 ≤ _
  nlinarith

def decode (q : Fraction) : Code × ℕ :=
  let n := BinaryNaturalView.decode q.num
  let d := BinaryNaturalView.decode q.den
  (⟨n.1,d.1,by rw [BinaryNaturalView.decode_value]; exact q.den_pos⟩,n.2+d.2+8)

@[simp] theorem decode_value (q : Fraction) : (decode q).1=BinaryRational.decode q := by
  simp [decode,BinaryNaturalView.decode_value,BinaryRational.decode]

theorem decode_paid {q : Fraction} {B : ℕ} (fit : StoredBounded q B) : (decode q).2 ≤ 40*(B+1)^2 := by
  have a := (BinaryNaturalView.decode_paid q.num).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right fit.1 1) 2))
  have b := (BinaryNaturalView.decode_paid q.den).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right fit.2 1) 2))
  have unit : 1 ≤ (B+1)^2 := Nat.one_le_pow _ _ (by omega)
  change (BinaryNaturalView.decode q.num).2+(BinaryNaturalView.decode q.den).2+8 ≤ _
  omega

private def binary (f : Fraction → Fraction → Fraction × ℕ) (a b : Code) : Code × ℕ :=
  let x := encode a
  let y := encode b
  let v := f x.1 y.1
  let result := decode v.1
  (result.1,x.2+y.2+v.2+result.2+8)

def add (a b : Code) : Code × ℕ := binary BinaryRational.add a b
def mul (a b : Code) : Code × ℕ := binary BinaryRational.mul a b
def div (a b : Code) : Code × ℕ := binary BinaryRational.div a b

@[simp] theorem add_value (a b : Code) : (add a b).1=a.add b := by
  simp only [add,binary,decode_value,BinaryRational.add_decode,encode_value]

@[simp] theorem mul_value (a b : Code) : (mul a b).1=a.mul b := by
  simp only [mul,binary,decode_value,BinaryRational.mul_decode,encode_value]

@[simp] theorem div_value (a b : Code) : (div a b).1=a.div b := by
  simp only [div,binary,decode_value,BinaryRational.div_decode,encode_value]

def budget {R : Type*} [Semiring R] (B : R) : R := 8192*(B+3)^2

private theorem binary_paid {a b : Code} {B : ℕ} (ha : a.Bounded B) (hb : b.Bounded B)
    (f : Fraction → Fraction → Fraction × ℕ)
    (bits : (f (encode a).1 (encode b).1).2 ≤ 2048*(B+2)^2)
    (result : StoredBounded (f (encode a).1 (encode b).1).1 (2*B+2)) :
    (binary f a b).2 ≤ budget B := by
  have work := decode_paid result
  have lhs := encode_paid ha
  have rhs := encode_paid hb
  change (encode a).2+(encode b).2+(f (encode a).1 (encode b).1).2+
    (decode (f (encode a).1 (encode b).1).1).2+8 ≤ _
  have size : (B+2)^2 ≤ (B+3)^2 := Nat.pow_le_pow_left (by omega) 2
  have resultSize : (2*B+3)^2 ≤ 4*(B+3)^2 :=
    (Nat.pow_le_pow_left (show 2*B+3≤2*(B+3) by omega) 2).trans_eq (by ring)
  change (decode (f (encode a).1 (encode b).1).1).2 ≤ 40*(2*B+3)^2 at work
  have unit : 1 ≤ (B+3)^2 := Nat.one_le_pow _ _ (by omega)
  unfold budget
  omega

theorem add_paid {a b : Code} {B : ℕ} (ha : a.Bounded B) (hb : b.Bounded B) : (add a b).2 ≤ budget B := by
  apply binary_paid ha hb _ (BinaryRational.add_charge (encode_width ha) (encode_width hb))
  have now := BinaryRational.add_stored_bounded (a:=(encode a).1) (b:=(encode b).1)
    (by simpa only [encode_value] using ha) (by simpa only [encode_value] using hb)
  simpa only [two_mul] using now

theorem mul_paid {a b : Code} {B : ℕ} (ha : a.Bounded B) (hb : b.Bounded B) : (mul a b).2 ≤ budget B := by
  apply binary_paid ha hb _ (BinaryRational.mul_charge (encode_width ha) (encode_width hb))
  have now := BinaryRational.mul_stored_bounded (a:=(encode a).1) (b:=(encode b).1)
    (by simpa only [encode_value] using ha) (by simpa only [encode_value] using hb)
  exact ⟨now.1.trans (by omega),now.2.trans (by omega)⟩

theorem div_paid {a b : Code} {B : ℕ} (ha : a.Bounded B) (hb : b.Bounded B) : (div a b).2 ≤ budget B := by
  apply binary_paid ha hb _ (BinaryRational.div_charge (encode_width ha) (encode_width hb))
  have now := BinaryRational.div_stored_bounded (a:=(encode a).1) (b:=(encode b).1)
    (by simpa only [encode_value] using ha) (by simpa only [encode_value] using hb)
  exact ⟨now.1.trans (by omega),now.2.trans (by omega)⟩

def le (a b : Code) : Bool × ℕ :=
  let x := encode a
  let y := encode b
  let result := BinaryRational.le x.1 y.1
  (result.1,x.2+y.2+result.2+6)

@[simp] theorem le_value (a b : Code) : (le a b).1=a.le b := by
  simp only [le,BinaryRational.le_decode,encode_value]

theorem le_paid {a b : Code} {B : ℕ} (ha : a.Bounded B) (hb : b.Bounded B) : (le a b).2 ≤ budget B := by
  have lhs := encode_paid ha
  have rhs := encode_paid hb
  have cmd := BinaryRational.le_charge (encode_width ha) (encode_width hb)
  change (BinaryRational.le (encode a).1 (encode b).1).2 ≤ 2048*(B+2)^2 at cmd
  have size : (B+2)^2 ≤ (B+3)^2 := Nat.pow_le_pow_left (by omega) 2
  have unit : 1 ≤ (B+3)^2 := Nat.one_le_pow _ _ (by omega)
  change (encode a).2+(encode b).2+(BinaryRational.le (encode a).1 (encode b).1).2+6 ≤ _
  unfold budget
  omega

def ceil (a : Code) : ℕ × ℕ :=
  let x := encode a
  let result := BinaryRationalCeiling.ceil x.1
  let n := BinaryNaturalView.decode result.1
  (n.1,x.2+result.2+n.2+6)

@[simp] theorem ceil_value (a : Code) : (ceil a).1=a.ceil := by
  simp only [ceil,BinaryNaturalView.decode_value,BinaryRationalCeiling.ceil_value,encode_value]

theorem ceil_paid {a : Code} {B : ℕ} (h : a.Bounded B) : (ceil a).2 ≤ budget B := by
  let b := BinaryRationalCeiling.ceil (encode a).1
  have x := encode_paid h
  have z := BinaryRationalCeiling.ceil_paid (encode_width h)
  have width : b.1.length ≤ B+2 := by
    rw [show b.1.length=(BinaryRational.decode (encode a).1).ceil.size from BinaryRationalCeiling.ceil_width _]
    rw [encode_value]
    have hsize := (Nat.size_le_size (Code.ceiling_intermediate h)).trans_eq Nat.size_pow
    unfold Code.ceil
    exact (Nat.size_le_size ((Nat.div_le_self ..).trans (Nat.sub_le ..))).trans hsize
  have r := (BinaryNaturalView.decode_paid b.1).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right width 1) 2))
  change (encode a).2+b.2+(BinaryNaturalView.decode b.1).2+6 ≤ _
  change b.2 ≤ _ at z
  unfold budget BinaryRationalCeiling.budget at *
  nlinarith

end DirectedFlowCutGap.BinaryRawRational
