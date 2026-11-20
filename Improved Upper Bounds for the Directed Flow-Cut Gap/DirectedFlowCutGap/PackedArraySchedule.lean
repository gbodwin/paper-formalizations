import DirectedFlowCutGap.CachedHeapBuild
import DirectedFlowCutGap.CachedWalkAddresses
import DirectedFlowCutGap.BinaryAllocationTrace

/-! Forget the types of retained slot values while preserving every array
instruction and reservation. This joins the three cache arrays without
changing their exact copy certificates. The schedules are proof witnesses. -/
namespace DirectedFlowCutGap.PackedArraySchedule

open ImmutableReferenceSimulation EncodedArrayStorage
open CachedReferenceHeap (Store push)
open CachedReferenceExecution (FastState)
open CachedHeapCopies (pushTrace payloadAfter addressAfter appendBlocks)

def shape {α : Type} : Instruction α → Instruction Unit
  | .reserve cells => .reserve cells
  | .storeHeader value => .storeHeader value
  | .load _ => .load ()
  | .loadLink => .loadLink
  | .store _ => .store ()
  | .storeLink => .storeLink
  | .advance => .advance
  | .branch => .branch

theorem shape_extent {α : Type} (code : List (Instruction α)) : fresh (code.map shape) = fresh code := by
  induction code with
  | nil => rfl
  | cons op rest ih =>
      cases op <;> simp [fresh, Instruction.fresh, shape] at ih ⊢ <;> omega

theorem shape_allocation {α : Type} (code : List (Instruction α)) (start : ℕ) :
    allocateTrace start (code.map shape) = allocateTrace start code := by
  induction code generalizing start with
  | nil => rfl
  | cons op rest ih => cases op <;> simp [shape, allocateTrace, ih]

theorem allocation_append {α : Type} (before after : List (Instruction α)) (start : ℕ) :
    let front := allocateTrace start before
    let tail := allocateTrace front.1 after
    allocateTrace start (before ++ after) = (tail.1, front.2 ++ tail.2) := by
  induction before generalizing start with
  | nil => simp [allocateTrace]
  | cons op rest ih => cases op <;> simp [allocateTrace, ih]

def appendCode (store : Store) (cell : Cell BinaryArithmetic.Bits) : List (Instruction Unit) :=
  (pushTrace store.cells cell).map shape ++
  (pushTrace store.cellPrefix (payloadAfter store cell)).map shape ++
  (pushTrace store.countPrefix (addressAfter store)).map shape

theorem append_count (store : Store) (cell : Cell BinaryArithmetic.Bits) :
    (appendCode store cell).length = 12 * store.cells.size + 23 ∧
      fresh (appendCode store cell) = 3 * store.cells.size + 11 := by
  obtain ⟨_, _, _, len, space⟩ := CachedHeapCopies.append_copies store cell
  simp only [appendCode, List.length_append, List.length_map, fresh_append, shape_extent]
  exact ⟨by omega, by omega⟩

theorem append_layout (store : Store) (cell : Cell BinaryArithmetic.Bits) (start : ℕ) :
    allocateTrace start (appendCode store cell) = appendBlocks store cell start := by
  simp only [appendCode, allocation_append, shape_allocation, appendBlocks, List.append_assoc]

def buildCode (store : Store) : Heap → List (Instruction Unit)
  | [] => []
  | cell::rest => appendCode store cell ++ buildCode (push store cell) rest

theorem build_schedule {store final : Store} {heap : Heap} {cells copies : ℕ}
    (built : CachedHeapBuild.Build store heap final cells copies) :
    (buildCode store heap).length = copies ∧ fresh (buildCode store heap) = cells ∧
      ∀ start, allocateTrace start (buildCode store heap) = CachedHeapBuild.placements store heap start := by
  induction built with
  | empty store => exact ⟨rfl, rfl, fun _ => rfl⟩
  | append store cell built ih =>
      obtain ⟨len, space⟩ := append_count store cell
      refine ⟨by simp only [buildCode, List.length_append, len, ih.1],
        by simp only [buildCode, fresh_append, space, ih.2.1], ?_⟩
      intro start
      simp only [buildCode, allocation_append, append_layout, ih.2.2, CachedHeapBuild.placements]

def stepCode {C : ℕ} (p : Program C) (s : FastState C) : List (Instruction Unit) :=
  match PaidCacheTrace.allocation p s with
  | none => []
  | some cell => appendCode s.store cell

theorem step_count {C : ℕ} (p : Program C) (s : FastState C) :
    (stepCode p s).length = (PaidCacheTrace.traffic p s).2 ∧
      fresh (stepCode p s) = (PaidCacheTrace.traffic p s).1 := by
  unfold stepCode PaidCacheTrace.traffic
  cases PaidCacheTrace.allocation p s with
  | none => exact ⟨rfl, rfl⟩
  | some c => exact append_count s.store c

theorem step_layout {C : ℕ} (p : Program C) (s : FastState C) (start : ℕ) :
    allocateTrace start (stepCode p s) = PaidCacheTrace.placeStep p s start := by
  unfold stepCode PaidCacheTrace.placeStep
  cases PaidCacheTrace.allocation p s with
  | none => rfl
  | some cell => exact append_layout _ cell _

theorem walk_schedule {C steps cells copies : ℕ} {p : Program C} {state out : FastState C}
    (walked : PaidCacheTrace.Walk p state steps cells copies out) :
    ∃ code : List (Instruction Unit), code.length = copies ∧ fresh code = cells ∧
      ∀ start, PaidCacheTrace.Layout p state start out
        (allocateTrace start code).1 (allocateTrace start code).2 := by
  induction walked with
  | done state => exact ⟨[], rfl, rfl, fun start => .done state start⟩
  | @step s next out k cells copies moved walked ih =>
      obtain ⟨tail, length, extent, placement⟩ := ih
      obtain ⟨firstLength, firstExtent⟩ := step_count p s
      refine ⟨stepCode p s ++ tail, by rw [List.length_append, firstLength, length],
        by rw [fresh_append, firstExtent, extent], ?_⟩
      intro start
      simp only [allocation_append, step_layout]
      exact .step moved (placement (PaidCacheTrace.placeStep p s start).1)

end DirectedFlowCutGap.PackedArraySchedule
