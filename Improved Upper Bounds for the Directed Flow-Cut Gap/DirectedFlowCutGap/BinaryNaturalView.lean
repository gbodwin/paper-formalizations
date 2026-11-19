import DirectedFlowCutGap.BinaryArithmetic

/-! Copy between natural-number fields and Boolean-list words, counting
the binary recursion, shifts, low-bit access and list work. -/

namespace DirectedFlowCutGap.BinaryNaturalView

open BinaryArithmetic

def encode (n : ℕ) : Bits × ℕ :=
  Nat.binaryRec ([],1) (fun b _ tail => (b::tail.1,tail.2+8*(tail.1.length+1)+8)) n

theorem encode_bits (n : ℕ) : (encode n).1=n.bits := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n h ih =>
    rw [encode,Nat.binaryRec_eq b n (Or.inr h),Nat.bits_append_bit n b h]
    change b::(encode n).1=b::n.bits
    rw [ih]

theorem encode_value (n : ℕ) : value (encode n).1=n := by rw [encode_bits,value_bits]

theorem encode_paid (n : ℕ) : (encode n).2 ≤ 16*(n.size+1)^2 := by
  induction n using Nat.binaryRec' with
  | zero => decide
  | bit b n h ih =>
    rw [encode,Nat.binaryRec_eq b n (Or.inr h),← Nat.size_eq_bits_len (n.bit b),Nat.bits_append_bit n b h]
    change (encode n).2+8*((encode n).1.length+1)+8 ≤ 16*((b::n.bits).length+1)^2
    rw [encode_bits,List.length_cons,Nat.size_eq_bits_len]
    nlinarith

def decode : Bits → ℕ × ℕ
  | [] => (0,1)
  | b::tail =>
    let result := decode tail
    (b.toNat+2*result.1,result.2+8*(tail.length+1)+4)

theorem decode_value (bits : Bits) : (decode bits).1=value bits := by
  induction bits with
  | nil => rfl
  | cons b tail ih => simp only [decode,value,ih]

theorem decode_paid (bits : Bits) : (decode bits).2 ≤ 16*(bits.length+1)^2 := by
  induction bits with
  | nil => decide
  | cons b tail ih =>
    simp only [decode,List.length_cons]
    nlinarith

end DirectedFlowCutGap.BinaryNaturalView
