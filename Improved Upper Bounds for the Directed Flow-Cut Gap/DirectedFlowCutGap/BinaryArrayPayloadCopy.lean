import DirectedFlowCutGap.PackedArrayReservations

/-! An explicit payload copy reads initialized bit words in order, copies each
bit, and advances the binary source and destination addresses. -/
namespace DirectedFlowCutGap.BinaryArrayPayloadCopy

open BinaryArithmetic

structure Slot where
  source : Bits
  destination : Bits
  word : Bits
  deriving Repr

structure Result where
  trace : List Slot
  charge : ℕ
  deriving Repr

private def wordCopy : Bits → Bits × ℕ
  | [] => ([],1)
  | b::bs =>
    let rest := wordCopy bs
    (b::rest.1,rest.2+2)

private theorem word_copy (word : Bits) : wordCopy word=(word,2*word.length+1) := by
  induction word with
  | nil => rfl
  | cons b bs ih =>
    simp only [wordCopy,ih,List.length_cons,Prod.mk.injEq,true_and]
    omega

def run (source destination : Bits) : List Bits → Result
  | [] => ⟨[],1⟩
  | head::tail =>
    let saved := wordCopy head
    let nextSource := addCanonical source [true]
    let nextDestination := addCanonical destination [true]
    let later := run nextSource.1 nextDestination.1 tail
    ⟨⟨source,destination,saved.1⟩::later.trace,
      saved.2+nextSource.2+nextDestination.2+4+later.charge⟩

def observe (slot : Slot) : ℕ × ℕ × Bits := (value slot.source,value slot.destination,slot.word)

def indexed (source destination : ℕ) : List Bits → List (ℕ × ℕ × Bits)
  | [] => []
  | x::xs => (source,destination,x)::indexed (source+1) (destination+1) xs

private theorem advance (a : Bits) :
    value (addCanonical a [true]).1=value a+1 ∧
      (addCanonical a [true]).1.length=(value a+1).size := by
  have h : value ([true] : Bits)=1 := rfl
  exact ⟨by rw [(canonical_values a [true]).1,h],by rw [(canonical_values a [true]).2.2.1,h]⟩

theorem refines (source destination : Bits) (words : List Bits) :
    (run source destination words).trace.map observe=indexed (value source) (value destination) words := by
  induction words generalizing source destination with
  | nil => rfl
  | cons x xs ih =>
    simp only [run,List.map_cons,observe,word_copy,indexed,ih,(advance source).1,(advance destination).1]

theorem words (source destination : Bits) (payload : List Bits) :
    (run source destination payload).trace.map Slot.word=payload := by
  induction payload generalizing source destination with
  | nil => rfl
  | cons x xs ih => simp only [run,List.map_cons,word_copy,ih]

private theorem index_read (source destination : ℕ) (payload : List Bits) (i : ℕ) (inside : i<payload.length) :
    (indexed source destination payload)[i]?=some (source+i,destination+i,payload[i]) := by
  induction payload generalizing source destination i with
  | nil => simp at inside
  | cons first rest ih =>
    cases i with
    | zero => simp [indexed]
    | succ j =>
      have h : j<rest.length := by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using inside
      have step (base : ℕ) : base+1+j=base+(j+1) := by omega
      simpa only [indexed,List.getElem?_cons_succ,List.getElem_cons_succ,step] using
        ih (source+1) (destination+1) j h

def initialized (base address : ℕ) (payload : List Bits) : Option Bits :=
  if base ≤ address then payload[address-base]? else none

theorem addressed (source destination : Bits) (payload : List Bits) (i : ℕ) (inside : i<payload.length) :
    ((run source destination payload).trace.map observe)[i]? =
      some (value source+i,value destination+i,payload[i]) ∧
    initialized (value source) (value source+i) payload=some payload[i] ∧
    initialized (value destination) (value destination+i) ((run source destination payload).trace.map Slot.word)=
      some payload[i] := by
  rw [refines,words]
  refine ⟨index_read _ _ _ _ inside,?_,?_⟩ <;>
    simp only [initialized,Nat.le_add_right,ite_true,Nat.add_sub_cancel_left,List.getElem?_eq_getElem inside]

def chargeBound (length addresses payload : ℕ) : ℕ :=
  length*(64*(addresses+2)+2*payload+5)+1

theorem charge_le (source destination : Bits) (payload : List Bits) {B W : ℕ}
    (src : source.length≤B) (dst : destination.length≤B)
    (srcEnd : (value source+payload.length).size≤B) (dstEnd : (value destination+payload.length).size≤B)
    (fits : ∀ word∈payload, word.length≤W) :
    (run source destination payload).charge≤chargeBound payload.length B W := by
  induction payload generalizing source destination with
  | nil => simp [run,chargeBound]
  | cons first rest ih =>
    let nextSource := addCanonical source [true]
    let nextDestination := addCanonical destination [true]
    have pos : 0 < value source+(first::rest).length := by simp
    have one : 1 ≤ B := (Nat.size_pos.mpr pos).trans_le srcEnd
    have plusSrc : value source+1+rest.length=value source+(first::rest).length := by
      simp only [List.length_cons]; omega
    have plusDst : value destination+1+rest.length=value destination+(first::rest).length := by
      simp only [List.length_cons]; omega
    have nextSrcEnd : (value nextSource.1+rest.length).size≤B := by
      rw [show value nextSource.1=value source+1 from (advance source).1,plusSrc]
      exact srcEnd
    have nextDstEnd : (value nextDestination.1+rest.length).size≤B := by
      rw [show value nextDestination.1=value destination+1 from (advance destination).1,plusDst]
      exact dstEnd
    have nextSrc : nextSource.1.length≤B := by
      rw [show nextSource.1.length=(value source+1).size from (advance source).2,← (advance source).1]
      exact (Nat.size_le_size (Nat.le_add_right (value nextSource.1) rest.length)).trans nextSrcEnd
    have nextDst : nextDestination.1.length≤B := by
      rw [show nextDestination.1.length=(value destination+1).size from (advance destination).2,← (advance destination).1]
      exact (Nat.size_le_size (Nat.le_add_right (value nextDestination.1) rest.length)).trans nextDstEnd
    have later := ih nextSource.1 nextDestination.1 nextSrc nextDst nextSrcEnd nextDstEnd
      (fun word member => fits word (List.mem_cons_of_mem _ member))
    have left : nextSource.2 ≤ 32*(B+2) := (canonical_charges src (show ([true] : Bits).length≤B from one)).1
    have right : nextDestination.2 ≤ 32*(B+2) := (canonical_charges dst (show ([true] : Bits).length≤B from one)).1
    have width := fits first List.mem_cons_self
    simp only [run,word_copy,List.length_cons,chargeBound,Nat.add_mul,Nat.one_mul] at later ⊢
    change 2*first.length+1+nextSource.2+nextDestination.2+4+(run nextSource.1 nextDestination.1 rest).charge ≤ _
    omega


/-- Slot addresses begin after the two length and capacity headers. -/
def blockCopy (source destination : ℕ) (payload : List Bits) : Result :=
  run (source+2).bits (destination+2).bits payload

open EncodedArrayStorage in
private theorem slot_copy_allocation (payload : List Bits) (start : ℕ) :
    allocateTrace start (copyTrace payload)=(start,[]) := by
  induction payload with
  | nil => rfl
  | cons word tail ih =>
    simp only [copyTrace,copyStep,List.cons_append,List.nil_append,allocateTrace,ih]

open EncodedArrayStorage in
theorem placed (source destination : ℕ) (payload : List Bits) (separate : source+2+payload.length≤destination) :
    let trace := reserveArray payload.length++copyTrace payload
    let allocation := allocateTrace destination trace
    let copied := blockCopy source destination payload
    allocation=(destination+(payload.length+2),[(destination,payload.length+2)]) ∧
      ∀ i : ℕ, ∀ inside : i<payload.length,
        (copied.trace.map observe)[i]?=some (source+2+i,destination+2+i,payload[i]) ∧
        source+2+i<destination ∧ destination ≤ destination+2+i ∧ destination+2+i<allocation.1 ∧
        initialized (source+2) (source+2+i) payload=some payload[i] ∧
        initialized (destination+2) (destination+2+i) (copied.trace.map Slot.word)=some payload[i] := by
  have layout : allocateTrace destination (reserveArray payload.length++copyTrace payload)=
      (destination+(payload.length+2),[(destination,payload.length+2)]) := by
    simp only [reserveArray,List.cons_append,List.nil_append,allocateTrace,slot_copy_allocation]
  refine ⟨layout,fun i inside => ?_⟩
  obtain ⟨slot,load,store⟩ := addressed (source+2).bits (destination+2).bits payload i inside
  simp only [value_bits] at slot load store
  refine ⟨slot,by omega,by omega,?_,load,store⟩
  rw [layout]
  dsimp only
  omega

theorem block_charge (source destination : ℕ) (payload : List Bits) {W : ℕ}
    (separate : source+2+payload.length≤destination) (fits : ∀ word∈payload, word.length≤W) :
    (blockCopy source destination payload).charge ≤
      chargeBound payload.length (destination+2+payload.length).size W := by
  let bound := destination+2+payload.length
  have a : source+2 ≤ bound := by dsimp only [bound]; omega
  have b : destination+2 ≤ bound := Nat.le_add_right _ _
  have endSource : source+2+payload.length ≤ bound := by dsimp only [bound]; omega
  exact charge_le (source+2).bits (destination+2).bits payload (B := bound.size) (W := W)
    (by rw [Nat.size_eq_bits_len]; exact Nat.size_le_size a)
    (by rw [Nat.size_eq_bits_len]; exact Nat.size_le_size b)
    (by rw [value_bits]; exact Nat.size_le_size endSource)
    (by rw [value_bits]) fits

end DirectedFlowCutGap.BinaryArrayPayloadCopy
