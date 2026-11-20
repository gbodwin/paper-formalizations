import DirectedFlowCutGap.DirectNaturalView

/-! Form the three indexes of a cached read by binary carry and borrow.
Compare the incoming address word with the actual array dimension. -/
namespace DirectedFlowCutGap.CachedBinaryIndex

open BinaryArithmetic

structure Indexes where
  address : ℕ
  successor : ℕ
  predecessor : ℕ
  inside : Bool
  work : ℕ

def compute (length : ℕ) (address : Bits) : Indexes :=
  let extent := DirectNaturalView.encode length
  let compare := BinaryArithmetic.compare address extent.1
  let after := increment true address
  let before := BinaryArithmetic.predecessor address
  let here := DirectNaturalView.decode address
  let next := DirectNaturalView.decode after.1
  let prior := DirectNaturalView.decode before.1
  ⟨here.1,next.1,prior.1,compare.less,
    extent.2+compare.steps+after.2+before.2+here.2+next.2+prior.2+8⟩

theorem values (length : ℕ) (address : Bits) :
    let index := compute length address
    index.address=value address ∧ index.successor=value address+1 ∧ index.predecessor=value address-1 ∧
      (index.inside=true ↔ value address<length) := by
  simp only [compute,DirectNaturalView.encode_eq,DirectNaturalView.decode_eq,BinaryNaturalView.decode_value,(increment_spec true address).1,Bool.toNat_true,
    (predecessor_spec address).1,(compare_spec ..).1,BinaryNaturalView.encode_value, and_self]

theorem paid {B length : ℕ} (address : Bits) (words : address.length≤B) (dimension : length.size≤B) :
    (compute length address).work≤128*(B+2)^2 := by
  let extent := BinaryNaturalView.encode length
  let after := increment true address
  let before := predecessor address
  have extentWidth : extent.1.length≤B := by
    rw [show extent.1=length.bits from BinaryNaturalView.encode_bits _,Nat.size_eq_bits_len]
    exact dimension
  have steps := (compare_spec address extent.1).2.2.trans
    (Nat.mul_le_mul_left 16 (Nat.add_le_add_right (max_le words extentWidth) 1))
  obtain ⟨_,afterWidth,afterWork⟩ := increment_spec true address
  obtain ⟨valueBefore,beforeWidth,beforeWork⟩ := predecessor_spec address
  have beforeBits : before.1.length≤B := by
    rw [show before.1.length=(value address-1).size from beforeWidth]
    exact ((Nat.size_le_size (Nat.sub_le _ _)).trans (Nat.size_le.mpr (value_lt address))).trans words
  have afterBits : after.1.length≤B+1 := afterWidth.trans (Nat.add_le_add_right words 1)
  have common : ∀ n≤B+1, 16*(n+1)^2 ≤ 16*(B+2)^2 := fun n h =>
    Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left (Nat.add_le_add_right h 1) 2)
  have extentWork := (BinaryNaturalView.encode_paid length).trans (common _ (dimension.trans (Nat.le_succ _)))
  have hereWork := (BinaryNaturalView.decode_paid address).trans (common _ (words.trans (Nat.le_succ _)))
  have nextWork := (BinaryNaturalView.decode_paid after.1).trans (common _ afterBits)
  have priorWork := (BinaryNaturalView.decode_paid before.1).trans (common _ (beforeBits.trans (Nat.le_succ _)))
  simp only [compute,DirectNaturalView.encode_eq,DirectNaturalView.decode_eq]
  change extent.2+(BinaryArithmetic.compare address extent.1).steps+after.2+before.2+
    (BinaryNaturalView.decode address).2+(BinaryNaturalView.decode after.1).2+
      (BinaryNaturalView.decode before.1).2+8≤_
  change after.2≤8*(address.length+1) at afterWork
  change before.2≤32*(address.length+1) at beforeWork
  nlinarith only [steps,afterWork,beforeWork,words,extentWork,hereWork,nextWork,priorWork,
    Nat.zero_le B,Nat.zero_le (B^2)]

end DirectedFlowCutGap.CachedBinaryIndex
