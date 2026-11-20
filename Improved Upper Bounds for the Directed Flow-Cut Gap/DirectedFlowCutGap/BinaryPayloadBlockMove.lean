import DirectedFlowCutGap.BinaryPayloadStore

/-! Copy a contiguous initialized array of bit words by reading and writing
the same store. A disjoint destination leaves the original data available. -/
namespace DirectedFlowCutGap.BinaryPayloadBlockMove

open BinaryArithmetic BinaryPayloadStore

def run (source destination : Bits) (store : Store) : ℕ → Option Store × ℕ
  | 0 => (some store,1)
  | remaining+1 =>
    let fetched := read source store.slots
    match fetched.1 with
    | none => (none,fetched.2+4)
    | some payload =>
      let updated := write store destination payload
      match updated.1 with
      | none => (none,fetched.2+updated.2+4)
      | some next =>
        let src := addCanonical source [true]
        let dst := addCanonical destination [true]
        let tail := run src.1 dst.1 next remaining
        (tail.1,fetched.2+updated.2+src.2+dst.2+tail.2+8)

def Segment (start : ℕ) (slots : List Slot) (payload : List Bits) : Prop :=
  ∀ i, ∀ h : i<payload.length, observe (start+i) slots=some payload[i]

private theorem increment (word : Bits) :
    value (addCanonical word [true]).1=value word+1 ∧
      (addCanonical word [true]).1.length=(value word+1).size := by
  have one : value ([true] : Bits)=1 := rfl
  rw [← one]
  exact ⟨(canonical_values word [true]).1,(canonical_values word [true]).2.2.1⟩

theorem run_preserves (source destination : Bits) (store : Store) (payload : List Bits)
    (separate : value source+payload.length≤value destination)
    (reserved : value destination+payload.length≤value store.next)
    (ready : Segment (value source) store.slots payload) :
    ∃ out, (run source destination store payload.length).1=some out ∧
      out.next=store.next ∧ Segment (value destination) out.slots payload ∧
      ∀ atAddress : ℕ, atAddress<value destination ∨ value destination+payload.length≤atAddress →
        observe atAddress out.slots=observe atAddress store.slots := by
  induction payload generalizing source destination store with
  | nil =>
    refine ⟨store,rfl,rfl,?_,fun _ _ => rfl⟩
    intro _ empty
    exact (Nat.not_lt_zero _ empty).elim
  | cons word rest ih =>
    let pushed : Store := ⟨store.next,⟨destination,word⟩::store.slots⟩
    let nextSource := (addCanonical source [true]).1
    let nextDestination := (addCanonical destination [true]).1
    have sourceValue : value nextSource=value source+1 := (increment source).1
    have destinationValue : value nextDestination=value destination+1 := (increment destination).1
    have readHead : (read source store.slots).1=some word := by
      rw [read_value]
      have first := ready 0 (by simp)
      change observe (value source+0) store.slots=some word at first
      simpa only [Nat.add_zero] using first
    have below : value destination<value store.next := by
      simp only [List.length_cons] at reserved
      omega
    have written : (write store destination word).1=some pushed := by
      rw [write_value,ite_eq_left below]
    have separated : value nextSource+rest.length≤value nextDestination := by
      rw [sourceValue,destinationValue]
      simp only [List.length_cons] at separate
      omega
    have kept : value nextDestination+rest.length≤value pushed.next := by
      rw [destinationValue]
      change value destination+1+rest.length≤value store.next
      simp only [List.length_cons] at reserved
      omega
    have readyTail : Segment (value nextSource) pushed.slots rest := by
      intro i inside
      have src : value nextSource+i=value source+(i+1) := by rw [sourceValue]; omega
      rw [src]
      change (if value destination=value source+(i+1) then some word
        else observe (value source+(i+1)) store.slots)=some rest[i]
      have different : value destination ≠ value source+(i+1) := by
        simp only [List.length_cons] at separate
        omega
      rw [ite_eq_right different]
      exact ready (i+1) (by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using inside)
    obtain ⟨out,ran,extent,copied,framed⟩ :=
      ih nextSource nextDestination pushed separated kept readyTail
    refine ⟨out,?_,extent,?_,?_⟩
    · rw [List.length_cons,run,readHead]
      dsimp only
      rw [written]
      exact ran
    · intro i inside
      cases i with
      | zero =>
        rw [Nat.add_zero,framed _ (.inl (by rw [destinationValue]; omega))]
        change (if value destination=value destination then some word else _) = some word
        rw [ite_eq_left rfl]
      | succ j =>
        have h : j<rest.length := by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using inside
        have atIndex : value destination+(j+1)=value nextDestination+j := by rw [destinationValue]; omega
        rw [atIndex]
        exact copied j h
    · intro atAddress untouched
      have other : value destination ≠ atAddress := by
        simp only [List.length_cons] at untouched
        omega
      have unchanged : atAddress<value nextDestination ∨ value nextDestination+rest.length≤atAddress := by
        rw [destinationValue]
        simp only [List.length_cons] at untouched
        omega
      rw [framed atAddress unchanged]
      change (if value destination=atAddress then some word else _) = _
      rw [ite_eq_right other]

def stepBudget {R : Type*} [Semiring R] (count B W : R) : R :=
  readBudget count B W+16*(B+1)+4*B+4*W+6+64*(B+2)+8

theorem run_paid (source destination : Bits) (store : Store) (count : ℕ) {B W : ℕ}
    (src : source.length≤B) (dst : destination.length≤B) (limit : store.next.length≤B)
    (endSource : (value source+count).size≤B) (endDestination : (value destination+count).size≤B)
    (slots : ∀ slot∈store.slots, slot.address.length≤B ∧ slot.payload.length≤W) :
    (run source destination store count).2 ≤ count*stepBudget (store.slots.length+count) B W+1 := by
  induction count generalizing source destination store with
  | zero => simp [run]
  | succ remaining ih =>
    let cap := store.slots.length+(remaining+1)
    have readCost := (read_paid source store.slots src slots).trans
      (show readBudget store.slots.length B W≤readBudget cap B W by
        unfold readBudget
        gcongr
        exact Nat.le_add_right _ _)
    have present : 1 ≤ B := (Nat.size_pos.mpr (show 0<value source+(remaining+1) by omega)).trans_le endSource
    have one : ([true] : Bits).length≤B := present
    have addSource := (canonical_charges src one).1
    have addDestination := (canonical_charges dst one).1
    let nextSource := (addCanonical source [true]).1
    let nextDestination := (addCanonical destination [true]).1
    have srcEnd : (value nextSource+remaining).size≤B := by
      rw [show value nextSource=value source+1 from (increment source).1,
        show value source+1+remaining=value source+(remaining+1) by omega]
      exact endSource
    have dstEnd : (value nextDestination+remaining).size≤B := by
      rw [show value nextDestination=value destination+1 from (increment destination).1,
        show value destination+1+remaining=value destination+(remaining+1) by omega]
      exact endDestination
    have srcWidth : nextSource.length≤B := by
      rw [show nextSource.length=(value source+1).size from (increment source).2,← (increment source).1]
      exact (Nat.size_le_size (Nat.le_add_right (value nextSource) remaining)).trans srcEnd
    have dstWidth : nextDestination.length≤B := by
      rw [show nextDestination.length=(value destination+1).size from (increment destination).2,
        ← (increment destination).1]
      exact (Nat.size_le_size (Nat.le_add_right (value nextDestination) remaining)).trans dstEnd
    rw [run]
    dsimp only
    cases loaded : (read source store.slots).1 with
    | none =>
      change (read source store.slots).2+4≤_
      rw [Nat.succ_mul]
      change _≤remaining*stepBudget cap B W+stepBudget cap B W+1
      unfold stepBudget
      omega
    | some word =>
      dsimp only
      have wordWidth := found_word_fits source store.slots word loaded (fun cell h => (slots cell h).2)
      have writeCost := write_paid store destination word limit dst wordWidth
      cases saved : (write store destination word).1 with
      | none =>
        change (read source store.slots).2+(write store destination word).2+4≤_
        rw [Nat.succ_mul]
        change _≤remaining*stepBudget cap B W+stepBudget cap B W+1
        unfold stepBudget
        omega
      | some next =>
        have contents : next=⟨store.next,⟨destination,word⟩::store.slots⟩ := by
          rw [write_value] at saved
          split at saved
          · exact (Option.some.inj saved).symm
          · cases saved
        have ready : ∀ slot∈next.slots, slot.address.length≤B ∧ slot.payload.length≤W := by
          rw [contents]
          intro slot h
          simp only [List.mem_cons] at h
          rcases h with equal | old
          · subst slot
            exact ⟨dst,wordWidth⟩
          · exact slots slot old
        have nextLimit : next.next.length≤B := by rw [contents]; exact limit
        have size : next.slots.length+remaining=cap := by
          rw [contents]
          dsimp only [cap]
          simp only [List.length_cons]
          omega
        have later := ih nextSource nextDestination next srcWidth dstWidth nextLimit srcEnd dstEnd ready
        rw [size] at later
        change (read source store.slots).2+(write store destination word).2+
          (addCanonical source [true]).2+(addCanonical destination [true]).2+
          (run nextSource nextDestination next remaining).2+8≤_
        rw [Nat.succ_mul]
        change _≤remaining*stepBudget cap B W+stepBudget cap B W+1
        unfold stepBudget at later ⊢
        omega

end DirectedFlowCutGap.BinaryPayloadBlockMove
