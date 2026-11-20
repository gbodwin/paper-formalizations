import DirectedFlowCutGap.CachedHeapCopies
import DirectedFlowCutGap.CachedReferenceExecution

/-! The reference-to-cache conversion performs the actual left fold of the
three-array append. Its storage certificate uses the same persistent-copy
semantics as the subsequent charged driver. -/
namespace DirectedFlowCutGap.CachedHeapBuild

open BinaryArithmetic ImmutableReferenceSimulation
open CachedReferenceHeap (Store push empty)
open CachedReferenceExecution (FastState)
open CachedHeapCopies (appendBlocks append_end append_address)

inductive Build : Store → Heap → Store → ℕ → ℕ → Prop where
  | empty (s : Store) : Build s [] s 0 0
  | append (s : Store) (cell : Cell Bits) {rest : Heap} {result : Store} {cells copies : ℕ} :
      Build (push s cell) rest result cells copies →
      Build s (cell::rest) result (3*s.cells.size+11+cells) (12*s.cells.size+23+copies)

private theorem push_size (s : Store) (cell : Cell Bits) : (push s cell).cells.size=s.cells.size+1 :=
  Array.size_push cell

theorem fold_copies (s : Store) (heap : Heap) :
    ∃ cells copies, Build s heap (heap.foldl push s) cells copies ∧
      cells ≤ heap.length*(3*(s.cells.size+heap.length)+11) ∧
      copies ≤ heap.length*(12*(s.cells.size+heap.length)+23) := by
  induction heap generalizing s with
  | nil => exact ⟨0,0,.empty s,by simp,by simp⟩
  | cons cell rest ih =>
      obtain ⟨cells,copies,tail,space,work⟩ := ih (push s cell)
      have count : (push s cell).cells.size+rest.length=s.cells.size+(rest.length+1) := by rw [push_size]; omega
      rw [count] at space work
      refine ⟨_,_,.append s cell tail,?_,?_⟩
      all_goals
        rw [List.length_cons,Nat.add_mul,Nat.one_mul]
        omega

theorem original_build {C : ℕ} (state : BitState C) :
    ∃ cells copies, Build empty state.heap (FastState.ofReference state).store cells copies ∧
      cells ≤ state.heap.length*(3*state.heap.length+11) ∧
      copies ≤ state.heap.length*(12*state.heap.length+23) := by
  change ∃ cells copies, Build empty state.heap (state.heap.foldl push empty) cells copies ∧ _
  have initial : empty.cells.size=0 := rfl
  simpa only [initial,Nat.zero_add] using fold_copies empty state.heap

/-- Allocate the three arrays in the actual order of the initial cache fold. -/
def placements (s : Store) : Heap → ℕ → ℕ × List (ℕ × ℕ)
  | [],start => (start,[])
  | c::rest,start =>
      let placed := appendBlocks s c start
      let later := placements (push s c) rest placed.1
      (later.1,placed.2++later.2)

theorem Build.placement {s out : Store} {heap : Heap} {cells copies : ℕ}
    (built : Build s heap out cells copies) (start : ℕ) :
    (placements s heap start).1=start+cells ∧
      ∀ block ∈ (placements s heap start).2, ∀ offset<block.2,
        start ≤ block.1+offset ∧ block.1+offset < start+cells := by
  induction built generalizing start with
  | empty s => simp [placements]
  | @append s c rest result cells copies built ih =>
      let placed := appendBlocks s c start
      let later := placements (push s c) rest placed.1
      have firstEnd : placed.1=start+3*s.cells.size+11 := append_end s c start
      obtain ⟨endAll,width⟩ := ih placed.1
      change later.1=placed.1+cells at endAll
      change later.1=start+(3*s.cells.size+11+cells) ∧
        ∀ block ∈ placed.2++later.2, ∀ offset<block.2,
          start≤block.1+offset ∧ block.1+offset<start+(3*s.cells.size+11+cells)
      refine ⟨by omega,?_⟩
      intro block found offset valid
      rcases List.mem_append.mp found with earlier|after
      · obtain ⟨lo,hi⟩ := append_address earlier offset valid
        exact ⟨lo,hi.trans_le (by omega)⟩
      · obtain ⟨lo,hi⟩ := width block after offset valid
        constructor <;> omega

end DirectedFlowCutGap.CachedHeapBuild
