import DirectedFlowCutGap.GuardedFuelFreeRounding
import DirectedFlowCutGap.PackedStoragePolynomial
import DirectedFlowCutGap.PackedArrayReservations

/-! Place the modeled persistent arrays of the actual packed run and its
terminal mask on one address space after the supplied input cells. -/
namespace DirectedFlowCutGap.GuardedPackedArrayPlan

open BinaryArithmetic ImmutableReferenceSimulation Polynomial
open RetainedGridState (PairFlags)
open CachedReferenceExecution (FastState)
open EncodedArrayStorage (Instruction allocateTrace fresh)
open PackedArraySchedule (buildCode)
open PackedArrayReservations (maskCode)
open PhysicalIntegerRounding (boundaryWords Result)
open GuardedFuelFreeRounding (hard packed_input hard_result)
open RawGraphInputStore (prepare)
open RawGraphControllerProgram (program)

def maskWord (reached : Option (FastState 26704)) : Option Bits :=
  reached.bind (fun out => (CachedGuardedMaskReadback.measure out).1.1)

structure ArrayPlan (initial : BitState 26704) (n : ℕ) (reached : Option (FastState 26704))
    (code : List (Instruction Unit)) : Prop where
  schedule : ∃ buildCells buildCopies steps runCells runCopies stop walkCode,
    CachedHeapBuild.Build CachedReferenceHeap.empty initial.heap
      (FastState.ofReference initial).store buildCells buildCopies ∧
    PaidCacheTrace.Walk program (FastState.ofReference initial) steps runCells runCopies stop ∧
    code = buildCode CachedReferenceHeap.empty initial.heap ++ walkCode ++ maskCode n (maskWord reached) ∧
    (match reached with
    | none => TotalGuardedPackedExecution.blocked program stop
    | some final => final = stop ∧ program stop.pc = .halt) ∧
    ∀ start,
      let built := CachedHeapBuild.placements CachedReferenceHeap.empty initial.heap start
      let walk := allocateTrace (start+buildCells) walkCode
      let mask := allocateTrace (start+buildCells+runCells) (maskCode n (maskWord reached))
      PaidCacheTrace.Layout program (FastState.ofReference initial) built.1 stop
        (start+buildCells+runCells) walk.2 ∧
      (allocateTrace start code).2 = (built.2 ++ walk.2) ++ mask.2

theorem hard_arrays : ∃ cells copies : Polynomial ℕ,
    ∀ (n L T : ℕ) (adj : PairFlags n) (positive : 0 < L) (tape : Bits), L ≤ n →
    let words := boundaryWords n L T
    let entry := prepare (GraphRelaxationRefinement.matrix adj) words.dimension words.level words.trials tape
    let raw := PaidTotalRawGraphExecution.run entry.1 (packed_input adj L T tape) positive
    ∃ code : List (Instruction Unit),
      ArrayPlan entry.1 n raw.1 code ∧
      (match raw.1 with
      | none => (hard T adj L positive tape).1 = none
      | some out => ∃ bits : Bits, ∃ cut : Result n,
          maskWord raw.1 = some bits ∧ bits.length = n ∧
          (hard T adj L positive tape).1 = some cut ∧
          cut.mask = (MaskBoundaryAssembly.run n bits).1 ∧ cut.suffix = out.source) ∧
      fresh code ≤ cells.eval (n+T) ∧ code.length ≤ copies.eval (n+T) ∧
      ∀ start : ℕ,
        let execution := BinaryAllocationTrace.allocate start.bits (code.map BinaryAllocationTrace.reservation)
        let width := (start+cells.eval (n+T)).size
        (value execution.stop, execution.blocks.map (fun (a, b) => (value a, value b))) =
          allocateTrace start code ∧
        execution.charge ≤ BinaryAllocationTrace.chargeBound (copies.eval (n+T)) width ∧
        ∀ block ∈ (allocateTrace start code).2, ∀ offset < block.2, (block.1+offset).size ≤ width := by
  obtain ⟨space, work, bounded⟩ := PackedStoragePolynomial.polynomial
  let totalCells : Polynomial ℕ := space+(X^2+7*X+2)
  let totalCopies : Polynomial ℕ := work+(2*X^2+21*X+4)
  refine ⟨totalCells, totalCopies, ?_⟩
  intro n L T adj positive tape allowed
  let words := boundaryWords n L T
  let entry := prepare (GraphRelaxationRefinement.matrix adj) words.dimension words.level words.trials tape
  let data := packed_input adj L T tape
  let raw := PaidTotalRawGraphExecution.run entry.1 data positive
  let bitword := maskWord raw.1
  obtain ⟨buildCells, buildCopies, steps, runCells, runCopies, stop, built, walked, spaceBound, copyBound, observed⟩ :=
    bounded n L T adj entry.1 data positive allowed
  obtain ⟨walkCode, placed, traceLength, traceSpace, exactBlocks⟩ :=
    PackedArrayReservations.joins built walked n bitword
  let code := buildCode CachedReferenceHeap.empty entry.1.heap ++ walkCode ++ maskCode n bitword
  have nLe : n ≤ n+T := Nat.le_add_right _ _
  have sized : fresh code ≤ totalCells.eval (n+T) := by
    simp only [totalCells, eval_add, eval_mul, eval_pow, eval_X, eval_ofNat]
    exact traceSpace.trans (Nat.add_le_add spaceBound (by gcongr))
  have counted : code.length ≤ totalCopies.eval (n+T) := by
    simp only [totalCopies, eval_add, eval_mul, eval_pow, eval_X, eval_ofNat]
    exact traceLength.trans (Nat.add_le_add copyBound (by gcongr))
  refine ⟨code, ?_, ?_, sized, counted, ?_⟩
  · constructor
    exact ⟨buildCells, buildCopies, steps, runCells, runCopies, stop, walkCode, built, walked,
      rfl, observed, fun start => ⟨placed start, exactBlocks start⟩⟩
  · have proved := hard_result T adj L positive tape
    change (match raw.1 with
      | none => (hard T adj L positive tape).1 = none
      | some out => ∃ bits : Bits, ∃ cut : Result n,
          (CachedGuardedMaskReadback.measure out).1.1 = some bits ∧ bits.length = n ∧
          (hard T adj L positive tape).1 = some cut ∧
          cut.mask = (MaskBoundaryAssembly.run n bits).1 ∧ cut.suffix = out.source) at proved
    change (match raw.1 with
      | none => (hard T adj L positive tape).1 = none
      | some out => ∃ bits : Bits, ∃ cut : Result n,
          maskWord raw.1 = some bits ∧ bits.length = n ∧
          (hard T adj L positive tape).1 = some cut ∧
          cut.mask = (MaskBoundaryAssembly.run n bits).1 ∧ cut.suffix = out.source)
    cases reached : raw.1 <;> simpa only [reached, maskWord, Option.bind_some] using proved
  · intro start
    obtain ⟨exactWords, paid, addresses⟩ := PackedArrayReservations.binary_layout code start
    have wide : (start+fresh code).size ≤ (start+totalCells.eval (n+T)).size :=
      Nat.size_le_size (Nat.add_le_add_left sized _)
    exact ⟨exactWords, paid.trans (by unfold BinaryAllocationTrace.chargeBound; gcongr),
      fun block member offset inside => (addresses block member offset inside).trans wide⟩

end DirectedFlowCutGap.GuardedPackedArrayPlan
