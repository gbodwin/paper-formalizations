import DirectedFlowCutGap.CachedScalarRead
import DirectedFlowCutGap.CachedControllerStorage

/-! Use the measured binary counters to construct the same cached append.
The state, payload and address histories, and original charge are preserved. -/
namespace DirectedFlowCutGap.CachedBinaryAppend

open BinaryArithmetic ImmutableReferenceSimulation
open CachedReferenceHeap (Store)
open CachedHeapCopies (payloadAfter addressAfter)
open CachedScalarRead (sumMeasured sum_value sum_paid)

private def nextWord (length : ℕ) : Bits × ℕ :=
  let current := BinaryNaturalView.encode length
  let next := increment true current.1
  let common := trim next.1
  (common.1,current.2+next.2+common.2+4)

private theorem next_word (length : ℕ) : (nextWord length).1=(length+1).bits := by
  let current := BinaryNaturalView.encode length
  let next := increment true current.1
  have count := (increment_spec true current.1).1
  rw [show value current.1=length from BinaryNaturalView.encode_value _] at count
  have canon := trim_spec next.1
  change (trim next.1).1=(length+1).bits
  rw [← show value next.1=length+1 from count,← canon.2.1]
  exact (normal_bits canon.1).symm

private theorem next_paid {length W : ℕ} (fits : length.size≤W) : (nextWord length).2≤40*(W+2)^2 := by
  let current := BinaryNaturalView.encode length
  let next := increment true current.1
  have width : current.1.length≤W := by
    rw [show current.1=length.bits from BinaryNaturalView.encode_bits _,Nat.size_eq_bits_len]
    exact fits
  have charge := (BinaryNaturalView.encode_paid length).trans
    (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left (Nat.add_le_add_right fits 1) 2))
  have added := (increment_spec true current.1).2.2.trans
    (Nat.mul_le_mul_left 8 (Nat.add_le_add_right width 1))
  have nextWidth : next.1.length≤W+1 := (increment_spec true current.1).2.1.trans (Nat.add_le_add_right width 1)
  have trimmed := (trim_spec next.1).2.2.2.le.trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left 8 nextWidth) 1)
  change current.2+next.2+(trim next.1).2+4≤_
  nlinarith only [charge,added,trimmed,Nat.zero_le W,Nat.zero_le (W^2)]

structure Counters where
  payload : ℕ
  addresses : ℕ
  legacy : ℕ
  work : ℕ

private def counterRead (a : Array ℕ) (index : ℕ) : ℕ := a[index]?.getD 0

def counters (s : Store) (cell : Cell Bits) : Counters :=
  let length := s.cells.size
  let after := nextWord length
  let newLength := BinaryNaturalView.decode after.1
  let copied := copyCell cell
  let payload := sumMeasured [counterRead s.cellPrefix length,copied.2]
  let zero := isZero after.1
  let prior := predecessor after.1
  let addresses := sumMeasured [counterRead s.countPrefix length,zero.2,prior.2,6]
  let legacy := sumMeasured [payload.1,newLength.1,newLength.1]
  ⟨payload.1,addresses.1,legacy.1,
    after.2+newLength.2+copied.2+payload.2+zero.2+prior.2+addresses.2+legacy.2+2*(length.size+1)+16⟩

theorem counter_values (s : Store) (c : Cell Bits) :
    (counters s c).payload=payloadAfter s c ∧ (counters s c).addresses=addressAfter s ∧
      (counters s c).legacy=(CachedReferenceHeap.append s c).2 := by
  simp only [counters,payloadAfter,addressAfter,counterRead,sum_value,List.sum_cons,List.sum_nil,
    Nat.add_zero,next_word,BinaryNaturalView.decode_value,value_bits]
  constructor
  · trivial
  constructor
  · omega
  · have charged : (CachedReferenceHeap.append s c).2 =
        s.cellPrefix[s.cells.size]?.getD 0+(copyCell c).2+2*(s.cells.size+1) := rfl
    rw [charged]
    omega

private def store (s : Store) (c : Cell Bits) (accounting : Counters)
    (payload : accounting.payload=payloadAfter s c) (addresses : accounting.addresses=addressAfter s) : Store :=
  ⟨s.cells.push c,s.cellPrefix.push accounting.payload,s.countPrefix.push accounting.addresses,
    by simp only [Array.size_push,s.cell_size],by simp only [Array.size_push,s.count_size],
    by
      intro i inside
      rw [payload]
      exact (CachedReferenceHeap.append s c).1.cell_spec i inside,
    by
      intro i inside
      rw [addresses]
      exact (CachedReferenceHeap.append s c).1.count_spec i inside⟩

private def appendPrepared (s : Store) (c : Cell Bits) (accounting : Counters)
    (payload : accounting.payload=payloadAfter s c) (addresses : accounting.addresses=addressAfter s) : (Store × ℕ) × ℕ :=
  let updated := store s c accounting payload addresses
  ((updated,accounting.legacy),accounting.work)

def append (s : Store) (c : Cell Bits) : (Store × ℕ) × ℕ :=
  appendPrepared s c (counters s c) (counter_values s c).1 (counter_values s c).2.1

private theorem store_eq {a b : Store} (cells : a.cells=b.cells) (payload : a.cellPrefix=b.cellPrefix)
    (addresses : a.countPrefix=b.countPrefix) : a=b := by
  cases a
  cases b
  cases cells
  cases payload
  cases addresses
  rfl

private theorem prepared_value (s : Store) (c : Cell Bits) (accounting : Counters)
    (payload : accounting.payload=payloadAfter s c) (addresses : accounting.addresses=addressAfter s)
    (legacy : accounting.legacy=(CachedReferenceHeap.append s c).2) :
    (appendPrepared s c accounting payload addresses).1=CachedReferenceHeap.append s c := by
  dsimp only [appendPrepared]
  apply Prod.ext
  · apply store_eq
    · rfl
    · change s.cellPrefix.push accounting.payload=s.cellPrefix.push (payloadAfter s c)
      rw [payload]
    · change s.countPrefix.push accounting.addresses=s.countPrefix.push (addressAfter s)
      rw [addresses]
  · exact legacy

theorem value_eq (s : Store) (c : Cell Bits) : (append s c).1=CachedReferenceHeap.append s c := by
  unfold append
  apply prepared_value
  exact (counter_values s c).2.2

set_option maxHeartbeats 1200000 in
/-- The additional bound covers the actual binary scalar work of the append.
The separately certified three-array copy supplies its structural traffic. -/
theorem paid {s : Store} {c : Cell Bits} {H B : ℕ} (size : s.cells.size≤H)
    (bounded : Heap.Bounded B s.cells.toList) (cellFits : c.Bounded B) :
    (append s c).2≤1200*(CachedHeapWidths.readerWidth (H+1) B+2)^2 := by
  let W := CachedHeapWidths.readerWidth (H+1) B
  let length := s.cells.size
  let word := nextWord length
  let decoded := BinaryNaturalView.decode word.1
  let copied := copyCell c
  let payloadInputs := [counterRead s.cellPrefix length,copied.2]
  let countInputs := [counterRead s.countPrefix length,(isZero word.1).2,(predecessor word.1).2,6]
  let legacyInputs := [(sumMeasured payloadInputs).1,decoded.1,decoded.1]
  obtain ⟨oldWidth,newWidth,payloadWide,addressWide,chargedWide⟩ :=
    CachedControllerStorage.append_operands size bounded cellFits
  obtain ⟨payloadEq,addressEq,_⟩ := counter_values s c
  have wordWidth : word.1.length≤W := by
    rw [show word.1=(length+1).bits from next_word length,Nat.size_eq_bits_len]
    exact newWidth
  have w1 := next_paid oldWidth
  change word.2≤40*(W+2)^2 at w1
  have dec : decoded.2≤16*(W+1)^2 := (BinaryNaturalView.decode_paid word.1).trans
    (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left (Nat.add_le_add_right wordWidth 1) 2))
  have common : B≤W := le_max_left _ _
  have copy : copied.2≤8*(W+1) := (copyCell_bound cellFits).trans
    (Nat.mul_le_mul_left 8 (Nat.add_le_add_right common 1))
  have zero := (isZero_spec word.1).2.trans (Nat.mul_le_mul_left 4 (Nat.add_le_add_right wordWidth 1))
  have pred := (predecessor_spec word.1).2.2.trans (Nat.mul_le_mul_left 32 (Nat.add_le_add_right wordWidth 1))
  have width1 : payloadInputs.sum.size≤W := by
    rw [← sum_value,show (sumMeasured payloadInputs).1=payloadAfter s c from payloadEq]
    exact payloadWide
  have width2 : countInputs.sum.size≤W := by
    rw [← sum_value,show (sumMeasured countInputs).1=addressAfter s from addressEq]
    exact addressWide
  have width3 : legacyInputs.sum.size≤W := by
    have close : legacyInputs.sum=(CachedReferenceHeap.append s c).2 := by
      unfold legacyInputs decoded
      rw [sum_value,show word.1=(length+1).bits from next_word length,
        BinaryNaturalView.decode_value,value_bits]
      change _=counterRead s.cellPrefix length+copied.2+2*(length+1)
      simp only [payloadInputs,List.sum_cons,List.sum_nil,Nat.add_zero]
      omega
    rw [close]
    exact chargedWide
  have p := sum_paid payloadInputs width1
  have a := sum_paid countInputs width2
  have fees := sum_paid legacyInputs width3
  change (sumMeasured payloadInputs).2≤2*(96*(W+2)^2+4)+1 at p
  change (sumMeasured countInputs).2≤4*(96*(W+2)^2+4)+1 at a
  change (sumMeasured legacyInputs).2≤3*(96*(W+2)^2+4)+1 at fees
  change length.size≤W at oldWidth
  dsimp only [append,appendPrepared]
  change word.2+decoded.2+copied.2+(sumMeasured payloadInputs).2+(isZero word.1).2+
    (predecessor word.1).2+(sumMeasured countInputs).2+(sumMeasured legacyInputs).2+
      2*(length.size+1)+16≤1200*(W+2)^2
  nlinarith only [w1,dec,copy,zero,pred,p,a,fees,oldWidth,Nat.zero_le W,Nat.zero_le (W^2)]

end DirectedFlowCutGap.CachedBinaryAppend
