import DirectedFlowCutGap.ImmutableReferenceSimulation

/-! An addressed store for variable-length words. Latest writes shadow earlier
writes; reservation advances the first free address without reading the
store. Lookup compares the encoded addresses and copies the stored bits. -/
namespace DirectedFlowCutGap.BinaryPayloadStore

open BinaryArithmetic EncodedSequenceAccess
open ImmutableReferenceSimulation (copiedWord copiedWordCost)

structure Slot where
  address : Bits
  payload : Bits
  deriving Repr

structure Store where
  next : Bits
  slots : List Slot
  deriving Repr

def observe (address : ℕ) : List Slot → Option Bits
  | [] => none
  | slot::rest => if value slot.address=address then some slot.payload else observe address rest

def read (address : Bits) : List Slot → Option Bits × ℕ
  | [] => (none,1)
  | slot::rest =>
    let test := BinaryArithmetic.compare slot.address address
    if test.equal then
      let word := copyBits slot.payload
      (some word.1,test.steps+word.2+4)
    else
      let later := read address rest
      (later.1,test.steps+later.2+4)

theorem read_value (address : Bits) (slots : List Slot) :
    (read address slots).1=observe (value address) slots := by
  induction slots with
  | nil => rfl
  | cons slot rest ih =>
    have h := (compare_spec slot.address address).2.1
    by_cases equal : value slot.address=value address
    · simp only [read,observe,h.mpr equal,ite_true,copiedWord,equal]
    · have no : (BinaryArithmetic.compare slot.address address).equal ≠ true := h.not.mpr equal
      rw [read,ite_eq_right no,observe,ite_eq_right equal,ih]

def readBudget {R : Type*} [Semiring R] (count address payload : R) : R :=
  count*(16*(address+1)+4)+4*payload+2

theorem read_paid (address : Bits) (slots : List Slot) {B W : ℕ}
    (index : address.length ≤ B)
    (bounded : ∀ slot∈slots, slot.address.length ≤ B ∧ slot.payload.length ≤ W) :
    (read address slots).2 ≤ readBudget slots.length B W := by
  induction slots with
  | nil => simp [read,readBudget]
  | cons slot rest ih =>
    obtain ⟨width,payload⟩ := bounded slot List.mem_cons_self
    have compare := (compare_spec slot.address address).2.2.trans
      (Nat.mul_le_mul_left 16 (Nat.add_le_add_right (max_le width index) 1))
    have tail := ih (fun later mem => bounded later (List.mem_cons_of_mem _ mem))
    simp only [read]
    split <;> simp only [copiedWordCost,List.length_cons,readBudget,Nat.add_mul,Nat.one_mul] at *
    · have restNonneg : 0 ≤ rest.length*(16*(B+1)+4) := Nat.zero_le _
      omega
    · omega

def allocate (s : Store) (count : Bits) : (Store × Bits) × ℕ :=
  let extent := addCanonical s.next count
  let base := copyBits s.next
  ((⟨extent.1,s.slots⟩,base.1),extent.2+base.2+4)

theorem allocate_value (s : Store) (count : Bits) :
    value (allocate s count).1.1.next=value s.next+value count ∧
      (allocate s count).1.1.slots=s.slots ∧ (allocate s count).1.2=s.next := by
  simp only [allocate,copiedWord,(canonical_values s.next count).1,and_self]

theorem allocate_paid (s : Store) (count : Bits) {B : ℕ}
    (next : s.next.length ≤ B) (span : count.length ≤ B) :
    (allocate s count).2 ≤ 32*(B+2)+4*B+5 := by
  have h := (canonical_charges next span).1
  simp only [allocate,copiedWordCost]
  omega

def write (s : Store) (address word : Bits) : Option Store × ℕ :=
  let test := BinaryArithmetic.compare address s.next
  if test.less then
    let key := copyBits address
    let data := copyBits word
    (some ⟨s.next,⟨key.1,data.1⟩::s.slots⟩,test.steps+key.2+data.2+4)
  else (none,test.steps+4)

theorem write_value (s : Store) (address word : Bits) :
    (write s address word).1=
      if value address<value s.next then some ⟨s.next,⟨address,word⟩::s.slots⟩ else none := by
  have cmp := (compare_spec address s.next).1
  by_cases h : value address<value s.next
  · simp only [write,cmp.mpr h,h,ite_true,copiedWord]
  · rw [write,ite_eq_right (cmp.not.mpr h),ite_eq_right h]

theorem write_paid (s : Store) (address word : Bits) {B W : ℕ}
    (next : s.next.length≤B) (index : address.length≤B) (fits : word.length≤W) :
    (write s address word).2≤16*(B+1)+4*B+4*W+6 := by
  have h := (compare_spec address s.next).2.2.trans
    (Nat.mul_le_mul_left 16 (Nat.add_le_add_right (max_le index next) 1))
  simp only [write]
  split <;> simp only [copiedWordCost] <;> omega

theorem write_read (s : Store) (address word : Bits) {out : Store}
    (written : (write s address word).1=some out) (key : Bits) :
    (read key out.slots).1=
      if value key=value address then some word else (read key s.slots).1 := by
  rw [write_value] at written
  split at written
  · obtain rfl := Option.some.inj written
    simp only [read_value,observe,eq_comm]
  · cases written

def Store.Valid (s : Store) : Prop := ∀ slot∈s.slots, value slot.address<value s.next

theorem allocate_valid (s : Store) (count : Bits) (valid : s.Valid) :
    (allocate s count).1.1.Valid := by
  intro slot mem
  rw [(allocate_value s count).1]
  rw [(allocate_value s count).2.1] at mem
  exact (valid slot mem).trans_le (Nat.le_add_right _ _)

theorem write_valid (s : Store) (address word : Bits) (valid : s.Valid) {out : Store}
    (written : (write s address word).1=some out) : out.Valid := by
  rw [write_value] at written
  split at written
  next fits =>
    obtain rfl := Option.some.inj written
    intro slot mem
    simp only [List.mem_cons] at mem
    rcases mem with same | old
    · subst slot
      exact fits
    · exact valid slot old
  · cases written

private theorem observe_missing (address : ℕ) (slots : List Slot)
    (missing : ∀ slot∈slots, value slot.address≠address) : observe address slots=none := by
  induction slots with
  | nil => rfl
  | cons slot rest ih =>
    rw [observe,ite_eq_right (missing slot List.mem_cons_self)]
    exact ih (fun later mem => missing later (List.mem_cons_of_mem _ mem))

theorem empty_above (s : Store) (valid : s.Valid) (address : Bits) (notAllocated : value s.next≤value address) :
    (read address s.slots).1=none := by
  rw [read_value]
  exact observe_missing (value address) s.slots
    (fun slot mem => ne_of_lt ((valid slot mem).trans_le notAllocated))

theorem found_word_fits (address : Bits) (slots : List Slot) (word : Bits)
    (observed : (read address slots).1=some word) {W : ℕ}
    (fits : ∀ slot∈slots, slot.payload.length≤W) : word.length≤W := by
  rw [read_value] at observed
  induction slots with
  | nil => cases observed
  | cons slot rest ih =>
    simp only [observe] at observed
    split at observed
    · obtain rfl := Option.some.inj observed
      exact fits slot List.mem_cons_self
    · exact ih observed (fun later mem => fits later (List.mem_cons_of_mem _ mem))

end DirectedFlowCutGap.BinaryPayloadStore
