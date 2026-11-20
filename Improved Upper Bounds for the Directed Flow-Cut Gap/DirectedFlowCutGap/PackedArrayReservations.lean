import DirectedFlowCutGap.PackedArraySchedule
import DirectedFlowCutGap.MaskBoundaryAssembly

/-! Bind the cache and terminal mask reservations to one binary bump-pointer
trace. The allocated arrays keep the copy semantics proved for each stage. -/
namespace DirectedFlowCutGap.PackedArrayReservations

open BinaryArithmetic ImmutableReferenceSimulation
open CachedReferenceExecution (FastState)
open CachedReferenceHeap (Store)
open EncodedArrayStorage (Instruction collectTrace fresh allocateTrace)
open PackedArraySchedule (shape buildCode)

def maskCode (n : ℕ) : Option Bits → List (Instruction Unit)
  | none => []
  | some bits => (collectTrace (MaskBoundaryAssembly.items n bits)).map shape

theorem mask_counts (n : ℕ) (word : Option Bits) :
    (maskCode n word).length ≤ 2*n^2+21*n+4 ∧ fresh (maskCode n word) ≤ n^2+7*n+2 := by
  cases word with
  | none => exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  | some bits =>
      obtain ⟨_, len, space⟩ := MaskBoundaryAssembly.copy_instructions n bits
      simpa only [maskCode, List.length_map, PackedArraySchedule.shape_extent] using ⟨len.le, space⟩

theorem mask_placement (n start : ℕ) (bits : Bits) :
    allocateTrace start (maskCode n (some bits)) =
      allocateTrace start (collectTrace (MaskBoundaryAssembly.items n bits)) :=
  PackedArraySchedule.shape_allocation _ _

theorem joins {C buildCells buildCopies steps runCells runCopies : ℕ}
    {p : Program C} {store : Store} {initial : BitState C} {stop : FastState C}
    (built : CachedHeapBuild.Build store initial.heap (FastState.ofReference initial).store buildCells buildCopies)
    (walked : PaidCacheTrace.Walk p (FastState.ofReference initial) steps runCells runCopies stop)
    (n : ℕ) (word : Option Bits) :
    ∃ walkCode : List (Instruction Unit),
      (∀ start, PaidCacheTrace.Layout p (FastState.ofReference initial)
        (CachedHeapBuild.placements store initial.heap start).1 stop
        (start+buildCells+runCells) (allocateTrace (start+buildCells) walkCode).2) ∧
      let full := buildCode store initial.heap ++ walkCode ++ maskCode n word
      full.length ≤ buildCopies+runCopies+(2*n^2+21*n+4) ∧
      fresh full ≤ buildCells+runCells+(n^2+7*n+2) ∧
      ∀ start, (allocateTrace start full).2 =
        ((CachedHeapBuild.placements store initial.heap start).2 ++
          (allocateTrace (start+buildCells) walkCode).2) ++
          (allocateTrace (start+buildCells+runCells) (maskCode n word)).2 := by
  obtain ⟨buildLen, buildExtent, buildPlaced⟩ := PackedArraySchedule.build_schedule built
  obtain ⟨walkCode, walkLen, walkExtent, walkPlaced⟩ := PackedArraySchedule.walk_schedule walked
  obtain ⟨maskLen, maskExtent⟩ := mask_counts n word
  have stage (start : ℕ) : (CachedHeapBuild.placements store initial.heap start).1 = start+buildCells :=
    (built.placement start).1
  have finish (start : ℕ) : (allocateTrace (start+buildCells) walkCode).1 = start+buildCells+runCells := by
    rw [EncodedArrayStorage.allocateTrace_end, walkExtent]
  refine ⟨walkCode, ?_, ?_, ?_, ?_⟩
  · intro start
    have layout := walkPlaced (start+buildCells)
    rw [finish start] at layout
    rw [stage start]
    exact layout
  · simp only [List.length_append, buildLen, walkLen]
    omega
  · simp only [EncodedArrayStorage.fresh_append, buildExtent, walkExtent]
    omega
  · intro start
    simp only [PackedArraySchedule.allocation_append, buildPlaced, stage, finish, List.append_assoc]

theorem binary_layout (code : List (Instruction Unit)) (start : ℕ) :
    let run := BinaryAllocationTrace.allocate start.bits (code.map BinaryAllocationTrace.reservation)
    let extent := start + fresh code
    (BinaryArithmetic.value run.stop, run.blocks.map (fun (a, b) => (value a, value b))) =
      allocateTrace start code ∧
    run.charge ≤ BinaryAllocationTrace.chargeBound code.length extent.size ∧
    ∀ block ∈ (allocateTrace start code).2, ∀ offset < block.2, (block.1+offset).size ≤ extent.size := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [value_bits] using BinaryAllocationTrace.allocate_refines code start.bits
  · have base : start.bits.length ≤ (start+fresh code).size := by
      exact (Nat.size_eq_bits_len start).le.trans (Nat.size_le_size (Nat.le_add_right _ _))
    exact BinaryAllocationTrace.allocate_charge code start.bits base (by rw [value_bits])
  · intro block member offset valid
    exact Nat.size_le_size (EncodedArrayStorage.allocated_address code start block member offset valid).2.le

end DirectedFlowCutGap.PackedArrayReservations
