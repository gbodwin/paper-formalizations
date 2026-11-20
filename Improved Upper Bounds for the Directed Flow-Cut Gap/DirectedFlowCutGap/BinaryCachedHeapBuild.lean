import DirectedFlowCutGap.CachedBinaryAppend
import DirectedFlowCutGap.CachedReferenceExecution

/-! Build the original cache through binary append counters. The recursion
uses the supplied heap and carries its allocation and counter costs in the
separate proof and work fields. -/
namespace DirectedFlowCutGap.BinaryCachedHeapBuild

open BinaryArithmetic ImmutableReferenceSimulation
open CachedReferenceHeap (Store push empty)
open CachedReferenceExecution (FastState)

def fold (s : Store) : Heap → Store × ℕ
  | [] => (s,0)
  | cell::rest =>
      let appended := CachedBinaryAppend.append s cell
      let tail := fold appended.1.1 rest
      (tail.1,appended.2+tail.2)

theorem fold_value (s : Store) (heap : Heap) : (fold s heap).1=heap.foldl push s := by
  induction heap generalizing s with
  | nil => rfl
  | cons cell rest ih =>
      simp only [fold,List.foldl_cons,CachedBinaryAppend.value_eq]
      exact ih (push s cell)

private theorem pushed_size (s : Store) (cell : Cell Bits) : (push s cell).cells.size=s.cells.size+1 :=
  Array.size_push cell

/-- The whole fold uses a common width derived from the final heap extent. -/
theorem fold_paid {H B : ℕ} (s : Store) (heap : Heap)
    (space : s.cells.size+heap.length≤H) (stored : Heap.Bounded B s.cells.toList)
    (incoming : Heap.Bounded B heap) :
    (fold s heap).2≤heap.length*(1200*(CachedHeapWidths.readerWidth (H+1) B+2)^2) := by
  induction heap generalizing s with
  | nil => simp [fold]
  | cons cell rest ih =>
      simp only [List.length_cons] at space ⊢
      have cellFit := incoming cell (List.mem_cons_self ..)
      have future : Heap.Bounded B (push s cell).cells.toList := by
        intro value membership
        rw [CachedReferenceHeap.push_value,List.mem_append,List.mem_singleton] at membership
        rcases membership with present|rfl
        · exact stored value present
        · exact cellFit
      have fits : (push s cell).cells.size+rest.length≤H := by rw [pushed_size]; omega
      have restFits : Heap.Bounded B rest := fun value present => incoming value (List.mem_cons_of_mem _ present)
      have appendPaid := CachedBinaryAppend.paid (show s.cells.size≤H by omega) stored cellFit
      have later := ih (push s cell) fits future restFits
      simp only [fold,CachedBinaryAppend.value_eq,Nat.add_mul,Nat.one_mul]
      exact (Nat.add_le_add appendPaid later).trans_eq (by ac_rfl)

def build {C : ℕ} (initial : BitState C) : FastState C × ℕ :=
  let cached := fold empty initial.heap
  (⟨cached.1,initial.next,initial.registers,initial.stack,initial.pc,initial.source⟩,cached.2)

theorem build_value {C : ℕ} (initial : BitState C) : (build initial).1=FastState.ofReference initial := by
  simp only [build,fold_value]
  rfl

theorem build_paid {C H B : ℕ} (initial : BitState C) (fits : initial.Bounded H B) :
    (build initial).2≤H*(1200*(CachedHeapWidths.readerWidth (H+1) B+2)^2) := by
  have records := fits.1
  unfold State.records at records
  have len : initial.heap.length≤H := by omega
  have emptySpace : empty.cells.size+initial.heap.length≤H := by simpa only [show empty.cells.size=0 from rfl,Nat.zero_add] using len
  have emptyFits : Heap.Bounded B empty.cells.toList := by
    intro elem present
    change elem ∈ ([] : Heap) at present
    simp at present
  exact (fold_paid empty initial.heap emptySpace emptyFits fits.2.2.1).trans (Nat.mul_le_mul_right _ len)

end DirectedFlowCutGap.BinaryCachedHeapBuild
