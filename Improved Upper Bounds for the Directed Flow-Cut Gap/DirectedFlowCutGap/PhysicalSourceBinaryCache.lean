import DirectedFlowCutGap.BinaryCompleteCacheExecution
import DirectedFlowCutGap.BinarySourceFuel
import DirectedFlowCutGap.OriginalGraphCostEnvelope

/-! Execute the original fractional source program in a binary cached driver.
Its proved full trace supplies termination even before a numeric fuel check. -/
namespace DirectedFlowCutGap.PhysicalSourceBinaryCache

open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal
open CachedReferenceExecution (FastState)
open PhysicalSourceDispatch (initial input program)

private def code : Vector (Instruction 13384) 13384 := Vector.ofFn program

private def dispatch (pc : Fin 13384) : Instruction 13384 := code.get pc

private theorem dispatch_eq : dispatch = program := by
  funext pc
  unfold dispatch code
  exact Vector.getElem_ofFn (f := program) pc.isLt

attribute [local irreducible] dispatch program

def reference (source : Bits) : Option (FastState 13384 × ℕ) :=
  let fuel := (BinarySourceFuel.compute source.length).1
  CachedReferenceExecution.execute program fuel (FastState.ofReference (initial source)) 0

private theorem cached_finishes {C k charge fuel : ℕ} {p : Program C} {start out : BitState C}
    {events : List Event} (ran : Run p k charge start events out)
    (halt : (attempt p out).result = none) (enough : k < fuel) :
    ∃ answer, CachedReferenceExecution.execute p fuel (FastState.ofReference start) 0 = some answer := by
  have complete := PhysicalCoverExecution.execute_eq ran halt fuel 0 enough
  rw [← PhysicalCoverExecution.executeCached_eq] at complete
  unfold PhysicalCoverExecution.executeCached at complete
  cases ready : CachedReferenceExecution.execute p fuel (FastState.ofReference start) 0 with
  | none => simp only [ready, Option.map_none, reduceCtorEq] at complete
  | some answer => exact ⟨answer, rfl⟩

set_option maxHeartbeats 800000 in
private theorem reference_finishes {n : ℕ} (D : BinaryFractionalGuesses.Input n)
    (source : Bits) (encoded : source = input D) : ∃ answer, reference source = some answer := by
  subst source
  obtain ⟨steps, charge, out, stepsFit, ran, halt, _, _, _⟩ := PhysicalSourceDispatch.bit_trace D
  let fuel := (BinarySourceFuel.compute (input D).length).1
  have enough : steps < fuel := by
    rw [show fuel = PhysicalSourceDispatch.instructionPolynomial.eval (input D).length+1 from
      BinarySourceFuel.fuel_value _]
    exact Nat.lt_succ_of_le (stepsFit.trans (PhysicalSourceDispatch.steps_polynomial D))
  unfold reference
  exact cached_finishes ran halt enough

private theorem initial_accessible {n : ℕ} (D : BinaryFractionalGuesses.Input n)
    (source : Bits) (encoded : source = input D) :
    Acc (BinaryCompleteCacheExecution.Next dispatch) (FastState.ofReference (initial source)) := by
  rw [dispatch_eq]
  obtain ⟨answer, seen⟩ := reference_finishes D source encoded
  unfold reference at seen
  exact BinaryCompleteCacheExecution.ready_of_success seen

def evaluate {n : ℕ} (D : BinaryFractionalGuesses.Input n) (source : Bits) (encoded : source = input D) :
    (FastState 13384 × ℕ) × ℕ :=
  BinaryCompleteCacheExecution.execute dispatch
    ⟨FastState.ofReference (initial source), initial_accessible D source encoded⟩ 0

theorem value_eq {n : ℕ} (D : BinaryFractionalGuesses.Input n) (source : Bits) (encoded : source = input D) :
    some (evaluate D source encoded).1 = reference source := by
  obtain ⟨answer, original⟩ := reference_finishes D source encoded
  rw [original]
  apply congrArg some
  unfold evaluate
  apply BinaryCompleteCacheExecution.observes (fuel := (BinarySourceFuel.compute source.length).1)
  change CachedReferenceExecution.execute dispatch (BinarySourceFuel.compute source.length).1
    (FastState.ofReference (initial source)) 0 = some answer
  rw [dispatch_eq]
  exact original

theorem output_bounds {n : ℕ} (D : BinaryFractionalGuesses.Input n) (source : Bits) (encoded : source = input D) :
    let fuel := (BinarySourceFuel.compute source.length).1
    (evaluate D source encoded).1.1.freeze.Bounded (1+fuel) fuel := by
  have projected := (value_eq D source encoded).symm
  unfold reference at projected
  have before : (FastState.ofReference (initial source)).freeze.Bounded 1 0 := by
    simp [CachedReferenceExecution.freeze_ofReference, initial, State.Bounded, State.records, Registers.All, Heap.Bounded]
  simpa only [Nat.zero_add] using BinaryCompleteCacheExecution.reached projected before

def budget (fuel : ℕ) : ℕ :=
  let width := 1+fuel
  let amount := fuel*stepBound 13384 width fuel
  fuel*(CachedBinaryAttempt.budget 13384 width fuel+BinaryGuardedCacheExecution.additionBudget amount)

theorem paid {n : ℕ} (D : BinaryFractionalGuesses.Input n) (source : Bits) (encoded : source = input D) :
    (evaluate D source encoded).2 ≤ budget ((BinarySourceFuel.compute source.length).1) := by
  obtain ⟨answer, original⟩ := reference_finishes D source encoded
  let fuel := (BinarySourceFuel.compute source.length).1
  let state : BinaryCompleteCacheExecution.Ready dispatch :=
    ⟨FastState.ofReference (initial source), initial_accessible D source encoded⟩
  have result : CachedReferenceExecution.execute dispatch fuel state.1 0 = some answer := by
    change CachedReferenceExecution.execute dispatch fuel (FastState.ofReference (initial source)) 0 = some answer
    rw [dispatch_eq]
    exact original
  have shape : state.1.freeze.Bounded 1 0 := by
    rw [show state.1.freeze = initial source from CachedReferenceExecution.freeze_ofReference _]
    simp [initial, State.Bounded, State.records, Registers.All, Heap.Bounded]
  have limit : 0+fuel*stepBound 13384 (1+fuel) fuel≤fuel*stepBound 13384 (1+fuel) fuel := by simp
  exact BinaryCompleteCacheExecution.paid result shape le_rfl (by simp) limit

open Polynomial OriginalGraphCostEnvelope in
theorem polynomial : ∃ p : Polynomial ℕ, ∀ {n : ℕ} (D : BinaryFractionalGuesses.Input n)
    (source : Bits) (encoded : source = input D), (evaluate D source encoded).2 ≤ p.eval source.length := by
  let fuel (length : ℕ) := (BinarySourceFuel.compute length).1
  have fuel_bound : Covered (fun x : ℕ => x) fuel := by
    refine ⟨PhysicalSourceDispatch.instructionPolynomial+1, fun x => ?_⟩
    rw [eval_add, eval_one, show fuel x = _ from BinarySourceFuel.fuel_value x]
  have costs : Covered (fun x : ℕ => x) (fun x => budget (fuel x)) := by
    simp only [budget, CachedBinaryAttempt.budget, CachedBinaryRegisterCopy.budget, CachedHeapWidths.readerWidth,
      CachedScalarRead.budget, CachedBinaryAttempt.sumsBudget, BinaryGuardedCacheExecution.additionBudget, stepBound]
    cover_arithmetic
  obtain ⟨p, cap⟩ := costs
  exact ⟨p, fun D source encoded => (paid D source encoded).trans (cap source.length)⟩

end DirectedFlowCutGap.PhysicalSourceBinaryCache
