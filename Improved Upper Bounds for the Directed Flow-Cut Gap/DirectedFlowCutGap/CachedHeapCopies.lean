import DirectedFlowCutGap.CachedReferenceHeap
import DirectedFlowCutGap.EncodedArrayStorage

/-! A persistent array push copies the retained slots to a fresh destination
and then stores the appended value. Use this allocation cost even if an
execution can reuse its existing array storage. -/
namespace DirectedFlowCutGap.CachedHeapCopies

open EncodedArrayStorage
open BinaryArithmetic ImmutableReferenceSimulation
open CachedReferenceHeap (Store)

def pushTrace {α : Type*} (xs : Array α) (x : α) : List (Instruction α) :=
  reserveArray (xs.size+1)++copyTrace xs.toList++[.store x]

inductive PushExec {α : Type*} (xs : Array α) (x : α) :
    Array α → List (Instruction α) → Prop where
  | write {copied : List α} (code : List (Instruction α)) :
      CopyExec xs.toList [] copied code →
      PushExec xs x (x::copied).reverse.toArray (reserveArray (xs.size+1)++code++[.store x])

theorem push_exec {α : Type*} (xs : Array α) (x : α) : PushExec xs x (xs.push x) (pushTrace xs x) := by
  have exec := PushExec.write (xs:=xs) (x:=x) (copyTrace xs.toList) (copy_exec xs.toList [])
  have result : (x::(xs.toList.reverse++[])).reverse.toArray=xs.push x := by
    apply Array.toList_inj.mp
    simp
  exact result ▸ exec

@[simp] theorem push_length {α : Type*} (xs : Array α) (x : α) :
    (pushTrace xs x).length=4*xs.size+5 := by
  simp only [pushTrace,List.length_append,reserveArray_length,copyTrace_length,Array.length_toList,
    List.length_cons,List.length_nil]
  omega

@[simp] theorem push_cells {α : Type*} (xs : Array α) (x : α) : fresh (pushTrace xs x)=xs.size+3 := by
  simp only [pushTrace,fresh_append,reserveArray_fresh,copyTrace_fresh]
  rfl

def payloadAfter (s : Store) (c : Cell Bits) : ℕ :=
  s.cellPrefix[s.cells.size]?.getD 0 + (copyCell c).2

def addressAfter (s : Store) : ℕ :=
  let word := (s.cells.size+1).bits
  s.countPrefix[s.cells.size]?.getD 0 + ((isZero word).2+(predecessor word).2+6)

/-- The three arrays are the actual cached heap fields. The two scalar
arguments to push are the retained cumulative counters of `append`. -/
theorem append_copies (s : Store) (c : Cell Bits) :
    let result := (CachedReferenceHeap.append s c).1
    let cells := pushTrace s.cells c
    let payloadCounters := pushTrace s.cellPrefix (payloadAfter s c)
    let addressCounters := pushTrace s.countPrefix (addressAfter s)
    PushExec s.cells c result.cells cells ∧
      PushExec s.cellPrefix (payloadAfter s c) result.cellPrefix payloadCounters ∧
      PushExec s.countPrefix (addressAfter s) result.countPrefix addressCounters ∧
      cells.length+payloadCounters.length+addressCounters.length=12*s.cells.size+23 ∧
      fresh cells+fresh payloadCounters+fresh addressCounters=3*s.cells.size+11 := by
  refine ⟨push_exec _ _,push_exec _ _,push_exec _ _,?_,?_⟩
  · simp only [push_length,s.cell_size,s.count_size]; omega
  · simp only [push_cells,s.cell_size,s.count_size]; omega

/-- A fresh address in a single persistent push is bounded independently of
how its index is encoded. The initial extent includes the source array. -/
theorem push_address_width {α : Type*} (xs : Array α) (x : α) (start : ℕ) (block : ℕ × ℕ)
    (allocated : block ∈ (allocateTrace start (pushTrace xs x)).2)
    (offset : ℕ) (valid : offset<block.2) :
    (block.1+offset).size ≤ (start+xs.size+3).size := by
  have space := (allocated_address (pushTrace xs x) start block allocated offset valid).2
  rw [push_cells] at space
  exact Nat.size_le_size (by omega)

/-- Place the three destination arrays in order after the existing extent. -/
def appendBlocks (s : Store) (c : Cell Bits) (start : ℕ) : ℕ × List (ℕ × ℕ) :=
  let heap := allocateTrace start (pushTrace s.cells c)
  let payload := allocateTrace heap.1 (pushTrace s.cellPrefix (payloadAfter s c))
  let address := allocateTrace payload.1 (pushTrace s.countPrefix (addressAfter s))
  (address.1,heap.2++payload.2++address.2)

theorem append_end (s : Store) (c : Cell Bits) (start : ℕ) :
    (appendBlocks s c start).1=start+3*s.cells.size+11 := by
  simp only [appendBlocks,allocateTrace_end,push_cells,s.cell_size,s.count_size]
  omega

theorem append_address {s : Store} {c : Cell Bits} {start : ℕ} {block : ℕ × ℕ}
    (allocated : block ∈ (appendBlocks s c start).2) (offset : ℕ) (valid : offset<block.2) :
    start ≤ block.1+offset ∧ block.1+offset < start+3*s.cells.size+11 := by
  let heap := allocateTrace start (pushTrace s.cells c)
  let payload := allocateTrace heap.1 (pushTrace s.cellPrefix (payloadAfter s c))
  let address := allocateTrace payload.1 (pushTrace s.countPrefix (addressAfter s))
  have hheap : heap.1=start+s.cells.size+3 := by
    simp only [heap,allocateTrace_end,push_cells,Nat.add_assoc]
  have hpayload : payload.1=heap.1+s.cells.size+4 := by
    simp only [payload,allocateTrace_end,push_cells,s.cell_size,Nat.add_assoc]
  change block ∈ (heap.2++payload.2)++address.2 at allocated
  rcases List.mem_append.mp allocated with previous | last
  · rcases List.mem_append.mp previous with first | second
    · have seen := allocated_address (pushTrace s.cells c) start block first offset valid
      rw [push_cells] at seen
      omega
    · have seen := allocated_address (pushTrace s.cellPrefix (payloadAfter s c)) heap.1 block second offset valid
      rw [push_cells,s.cell_size] at seen
      omega
  · have seen := allocated_address (pushTrace s.countPrefix (addressAfter s)) payload.1 block last offset valid
    rw [push_cells,s.count_size] at seen
    omega

theorem append_address_width {s : Store} {c : Cell Bits} {start : ℕ} {block : ℕ × ℕ}
    (allocated : block ∈ (appendBlocks s c start).2) (offset : ℕ) (valid : offset<block.2) :
    (block.1+offset).size ≤ (start+3*s.cells.size+11).size :=
  Nat.size_le_size ((append_address allocated offset valid).2.le)

end DirectedFlowCutGap.CachedHeapCopies
