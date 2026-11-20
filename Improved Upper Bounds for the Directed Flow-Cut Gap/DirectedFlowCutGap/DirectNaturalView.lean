import DirectedFlowCutGap.BinaryNaturalView

/-! Compute the same charged bit conversions without visiting each suffix
again to calculate its contribution to the recorded charge. -/
namespace DirectedFlowCutGap.DirectNaturalView

open BinaryArithmetic

private theorem encode_charge (n : ℕ) :
    (BinaryNaturalView.encode n).2 = 4*n.bits.length^2+12*n.bits.length+1 := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n hn ih =>
      rw [BinaryNaturalView.encode,Nat.binaryRec_eq b n (Or.inr hn),Nat.bits_append_bit n b hn]
      change (BinaryNaturalView.encode n).2+8*((BinaryNaturalView.encode n).1.length+1)+8 = _
      rw [BinaryNaturalView.encode_bits,ih,List.length_cons]
      ring

private theorem decode_charge (word : Bits) :
    (BinaryNaturalView.decode word).2=4*word.length^2+8*word.length+1 := by
  induction word with
  | nil => rfl
  | cons b rest ih =>
      simp only [BinaryNaturalView.decode,ih,List.length_cons]
      ring

def encode (n : ℕ) : Bits × ℕ :=
  let word := n.bits
  let width := word.length
  (word,4*width^2+12*width+1)

theorem encode_eq (n : ℕ) : encode n=BinaryNaturalView.encode n :=
  Prod.ext (BinaryNaturalView.encode_bits n).symm (encode_charge n).symm

def decode (word : Bits) : ℕ × ℕ :=
  let width := word.length
  (value word,4*width^2+8*width+1)

theorem decode_eq (word : Bits) : decode word=BinaryNaturalView.decode word :=
  Prod.ext (BinaryNaturalView.decode_value word).symm (decode_charge word).symm

end DirectedFlowCutGap.DirectNaturalView
