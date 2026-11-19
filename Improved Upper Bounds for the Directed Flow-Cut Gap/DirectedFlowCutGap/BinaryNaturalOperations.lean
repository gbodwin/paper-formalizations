import DirectedFlowCutGap.BinaryRawRational
import DirectedFlowCutGap.ChargedEdgeDyadicLabels

/-! Binary natural operations used by the numerical control parameters. -/

namespace DirectedFlowCutGap.BinaryNaturalOperations

open BinaryArithmetic RawNonnegativeRational

theorem ofNat_fit {n B : ℕ} (h : n.size ≤ B) : (Code.ofNat n).Bounded B :=
  ⟨(Nat.size_le.mp h).le,Nat.one_le_two_pow⟩

theorem size_le_self (n : ℕ) : n.size ≤ n := Nat.size_le.mpr n.lt_two_pow_self

def add (a b : ℕ) : ℕ × ℕ :=
  let q := BinaryRawRational.add (Code.ofNat a) (Code.ofNat b)
  (q.1.num,q.2+4)

@[simp] theorem add_value (a b : ℕ) : (add a b).1=a+b := by
  simp only [add,BinaryRawRational.add_value,Code.add,Code.ofNat,Nat.mul_one]

theorem add_paid {a b B : ℕ} (ha : a.size ≤ B) (hb : b.size ≤ B) : (add a b).2 ≤ BinaryRawRational.budget B+4 :=
  Nat.add_le_add_right (BinaryRawRational.add_paid (ofNat_fit ha) (ofNat_fit hb)) _

def mul (a b : ℕ) : ℕ × ℕ :=
  let q := BinaryRawRational.mul (Code.ofNat a) (Code.ofNat b)
  (q.1.num,q.2+4)

@[simp] theorem mul_value (a b : ℕ) : (mul a b).1=a*b := by
  simp only [mul,BinaryRawRational.mul_value,Code.mul,Code.ofNat]

theorem mul_paid {a b B : ℕ} (ha : a.size ≤ B) (hb : b.size ≤ B) : (mul a b).2 ≤ BinaryRawRational.budget B+4 :=
  Nat.add_le_add_right (BinaryRawRational.mul_paid (ofNat_fit ha) (ofNat_fit hb)) _

def ceilDiv (a b : ℕ) : ℕ × ℕ :=
  let x := BinaryRawRational.div (Code.ofNat a) (Code.ofNat b)
  let y := BinaryRawRational.ceil x.1
  (y.1,x.2+y.2+4)

@[simp] theorem ceilDiv_value (a b : ℕ) : (ceilDiv a b).1=a ⌈/⌉ b := by
  by_cases zero : b=0
  · simp [ceilDiv,zero,Code.div,Code.ofNat,Code.zero,Code.ceil]
  · simp only [ceilDiv,BinaryRawRational.ceil_value,BinaryRawRational.div_value,Code.div,Code.ofNat,
      zero,dite_false,Nat.mul_one,Nat.one_mul,Code.ceil,Nat.ceilDiv_eq_add_pred_div]

theorem ceilDiv_paid {a b B : ℕ} (ha : a.size ≤ B) (hb : b.size ≤ B) :
    (ceilDiv a b).2 ≤ 2*BinaryRawRational.budget (2*B)+4 := by
  let left := Code.ofNat a
  let right := Code.ofNat b
  let q := BinaryRawRational.div left right
  have f : q.1.Bounded (2*B) := by
    change (BinaryRawRational.div left right).1.Bounded _
    rw [BinaryRawRational.div_value,two_mul]
    exact Code.bounded_div (ofNat_fit ha) (ofNat_fit hb)
  have l := Code.bounded_mono (ofNat_fit ha) (show B ≤ 2*B by omega)
  have r := Code.bounded_mono (ofNat_fit hb) (show B ≤ 2*B by omega)
  have h : q.2 ≤ BinaryRawRational.budget (2*B) := BinaryRawRational.div_paid l r
  have c := BinaryRawRational.ceil_paid f
  change q.2+(BinaryRawRational.ceil q.1).2+4 ≤ _
  omega

def width (a : ℕ) : ℕ × ℕ :=
  let word := BinaryNaturalView.encode a
  (word.1.length,word.2+8*(word.1.length+1)^2+4)

@[simp] theorem width_value (a : ℕ) : (width a).1=a.size := by
  simp only [width,BinaryNaturalView.encode_bits,Nat.size_eq_bits_len]

theorem width_paid {a B : ℕ} (h : a.size ≤ B) : (width a).2 ≤ 24*(B+1)^2+4 := by
  have enc := BinaryNaturalView.encode_paid a
  have sq := Nat.pow_le_pow_left (Nat.add_le_add_right h 1) 2
  simp only [width,BinaryNaturalView.encode_bits,Nat.size_eq_bits_len]
  omega

def powerTwo (exponent : ℕ) : ℕ × ℕ :=
  let p := ChargedEdgeDyadicLabels.powerFraction exponent
  let x := BinaryNaturalView.decode p.den
  (x.1,x.2+8*(exponent+1)^2+4)

@[simp] theorem powerTwo_value (e : ℕ) : (powerTwo e).1=2^e := by
  have h := congrArg Code.den (ChargedEdgeDyadicLabels.decode_power e)
  change value (ChargedEdgeDyadicLabels.powerFraction e).den=(EncodedEdgeLabels.dyadicCode e).den at h
  have pos : (2:ℕ)^e ≠ 0 := pow_ne_zero _ (by decide)
  simp only [EncodedEdgeLabels.dyadicCode,Code.div,Code.one,Code.ofNat,pos,dite_false,Nat.one_mul] at h
  exact (BinaryNaturalView.decode_value _).trans h

theorem powerTwo_paid {e B : ℕ} (h : e ≤ B) : (powerTwo e).2 ≤ 24*(B+2)^2+4 := by
  have len := (ChargedEdgeDyadicLabels.power_width e).2.trans (Nat.add_le_add_right h 1)
  have dec := (BinaryNaturalView.decode_paid (ChargedEdgeDyadicLabels.powerFraction e).den).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right len 1) 2))
  change (BinaryNaturalView.decode (ChargedEdgeDyadicLabels.powerFraction e).den).2 ≤ 16*(B+2)^2 at dec
  have sq := Nat.pow_le_pow_left (show e+1 ≤ B+2 by omega) 2
  unfold powerTwo
  dsimp only
  omega

end DirectedFlowCutGap.BinaryNaturalOperations
