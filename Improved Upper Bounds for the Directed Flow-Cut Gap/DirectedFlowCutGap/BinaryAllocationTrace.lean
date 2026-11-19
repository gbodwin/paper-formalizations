import DirectedFlowCutGap.EncodedArrayStorage
import DirectedFlowCutGap.BinaryArithmetic

/-!
# Binary bump-pointer operations for retained array construction

Use the reserve instructions of the existing array-storage trace. The
allocation pass adds the actual binary block size to the current pointer.
It returns the same ordered blocks and end pointer as the natural trace.
The charge covers this pass and its binary additions. Slot traffic,
reference payloads and materialization of the trace remain separate.
-/

namespace DirectedFlowCutGap.BinaryAllocationTrace

open BinaryArithmetic EncodedArrayStorage

structure Result where
  stop : Bits
  blocks : List (Bits × Bits)
  charge : ℕ

def allocate (start : Bits) : List (Option Bits) → Result
  | [] => ⟨start, [], 1⟩
  | none :: rest =>
    let tail := allocate start rest
    ⟨tail.stop, tail.blocks, tail.charge + 4⟩
  | some cells :: rest =>
    let next := addCanonical start cells
    let tail := allocate next.1 rest
    ⟨tail.stop, (start, cells) :: tail.blocks, tail.charge + next.2 + 8⟩

def reservation {A : Type} : Instruction A → Option Bits
  | .reserve cells => some cells.bits
  | _ => none

theorem allocate_refines {A : Type} (trace : List (Instruction A)) (start : Bits) :
    let r := allocate start (trace.map reservation)
    (value r.stop, r.blocks.map (fun (a, b) => (value a, value b))) = allocateTrace (value start) trace := by
  induction trace generalizing start with
  | nil => rfl
  | cons op tail ih =>
    cases op with
    | reserve cells =>
      have he := ih (addCanonical start cells.bits).1
      simp only [(canonical_values start cells.bits).1, value_bits] at he
      simp only [List.map_cons, reservation, allocate, allocateTrace, value_bits]
      rw [← he]
    | storeHeader _ | load _ | loadLink | store _ | storeLink | advance | branch =>
      exact ih start

def chargeBound (steps B : ℕ) : ℕ := steps * (32 * (B + 2) + 8) + 1

theorem allocate_charge {A : Type} (trace : List (Instruction A)) (start : Bits) {B : ℕ}
    (hs : start.length ≤ B) (he : (value start + fresh trace).size ≤ B) :
    (allocate start (trace.map reservation)).charge ≤ chargeBound trace.length B := by
  induction trace generalizing start with
  | nil => simp [allocate, chargeBound]
  | cons op tail ih =>
    cases op with
    | reserve cells =>
      have hsize : (value start + cells + fresh tail).size ≤ B := by
        simpa [fresh, Instruction.fresh, Nat.add_assoc] using he
      have hc : cells ≤ value start + cells + fresh tail := by omega
      have hn : value start + cells ≤ value start + cells + fresh tail := by omega
      have hb : cells.bits.length ≤ B := by
        rw [Nat.size_eq_bits_len]
        exact (Nat.size_le_size hc).trans hsize
      let next := addCanonical start cells.bits
      have hv : value next.1 = value start + cells := by simp [next, (canonical_values start cells.bits).1, value_bits]
      have hl : next.1.length = (value start + cells).size := by
        simp [next, (canonical_values start cells.bits).2.2.1, value_bits]
      have ht := ih next.1 (hl.le.trans ((Nat.size_le_size hn).trans hsize)) (by rwa [hv])
      have hn' := (canonical_charges hs hb).1
      simp only [List.map_cons, reservation, allocate, List.length_cons, chargeBound] at ht ⊢
      rw [Nat.add_mul, Nat.one_mul]
      change (allocate next.1 (tail.map reservation)).charge + next.2 + 8 ≤ _
      exact (Nat.add_le_add_right (Nat.add_le_add ht hn') 8).trans (by omega)
    | storeHeader _ | load _ | loadLink | store _ | storeLink | advance | branch =>
      have ht := ih start hs (by simpa [fresh, Instruction.fresh] using he)
      simp only [List.map_cons, reservation, allocate, List.length_cons, chargeBound] at ht ⊢
      rw [Nat.add_mul, Nat.one_mul]
      omega

/-- Collection's actual explicit reserve trace has a polynomial extent.
The width includes the input pointer, even when its word has padding. -/
theorem collect_reservations {A : Type} (xs : List (A × ℕ)) (start : Bits) :
    let extent := value start + (xs.length ^ 2 + 7 * xs.length + 2)
    let B := max start.length extent.size
    let r := allocate start ((collectTrace xs).map reservation)
    value r.stop = value start + collectCells xs.length ∧
      r.charge ≤ chargeBound (2 * xs.length ^ 2 + 21 * xs.length + 4) B := by
  have h := allocate_refines (collectTrace xs) start
  have hstop := congrArg Prod.fst h
  dsimp only at hstop
  rw [allocateTrace_end, collectTrace_fresh] at hstop
  refine ⟨hstop, ?_⟩
  rw [← collectTrace_length]
  apply allocate_charge (collectTrace xs) start (le_max_left _ _)
  rw [collectTrace_fresh]
  apply le_trans _ (le_max_right _ _)
  exact Nat.size_le_size (Nat.add_le_add_left (collectCells_bound xs.length) (value start))

end DirectedFlowCutGap.BinaryAllocationTrace
