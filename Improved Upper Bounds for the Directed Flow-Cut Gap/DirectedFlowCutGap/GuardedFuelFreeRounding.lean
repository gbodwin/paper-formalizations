import DirectedFlowCutGap.PaidTotalRawGraphExecution
import DirectedFlowCutGap.GuardedIntegerRoundingWorkBounds

/-! Reuse the exact packed inputs and output reader while erasing the fuel
calculation from the executed hard branch. -/
namespace DirectedFlowCutGap.GuardedFuelFreeRounding

open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal
open RetainedGridState (PairFlags)
open OriginalGraphCostEnvelope (preparedCells preparedCells_eq)
open PhysicalIntegerRounding (Result boundaryWords)
open RawGraphControllerProgram (instructionBound program)
open RawGraphInputStore (prepare)
open PhysicalCoverAccess (Read)
open CachedReferenceExecution (FastState)
open GuardedIntegerRoundingWork (collect runPacked)

private theorem input {n : ℕ} (adj : PairFlags n) (L T : ℕ) (tape : Bits) :
    let words := boundaryWords n L T
    let entry := prepare (GraphRelaxationRefinement.matrix adj) words.dimension words.level words.trials tape
    let H := preparedCells n L T
    RawGraphControllerLaw.Input (L:=L) adj T.bits (H+1) H entry.1 := by
  dsimp only
  simp only [PhysicalIntegerRounding.boundary_dimension,PhysicalIntegerRounding.boundary_level,
    PhysicalIntegerRounding.boundary_trials]
  simpa only [preparedCells_eq adj L T] using (RawGraphInputStore.prepare_spec (L:=L) adj T.bits tape).1

def hard {n : ℕ} (T : ℕ) (adj : PairFlags n) (L : ℕ) (positive : 0<L) (tape : Bits) : Read (Result n) :=
  let words := boundaryWords n L T
  let entry := prepare (GraphRelaxationRefinement.matrix adj) words.dimension words.level words.trials tape
  let run := PaidTotalRawGraphExecution.run entry.1 (input adj L T tape) positive
  collect entry.2 words.paid 0 run

private theorem collect_control {n : ℕ} (prepared boundary fee : ℕ) (run : Option (FastState 26704) × ℕ) :
    collect (n:=n) prepared boundary fee run =
      ((collect (n:=n) prepared boundary 0 run).1,(collect (n:=n) prepared boundary 0 run).2+fee) := by
  unfold collect
  cases run.1 with
  | none => rfl
  | some out =>
      dsimp only
      cases (GuardedIntegerRoundingWork.readMask out).1 <;> rfl

private theorem compare_collect (n : ℕ) (entry : BitState 26704 × ℕ) (boundary amount : ℕ)
    (result : Option (FastState 26704) × ℕ)
    (value : result=PaidGuardedExecution.execute program amount (FastState.ofReference entry.1) 0) :
    let fresh := collect (n:=n) entry.2 boundary 0 result
    let old := runPacked n entry boundary amount
    fresh.1=old.1 ∧ fresh.2 ≤ old.2 := by
  let encoded := BinaryNaturalView.encode amount
  let ran := PaidGuardedExecution.executeBinary program encoded.1 (FastState.ofReference entry.1) 0
  have prior := (PaidGuardedExecution.binary_spec program encoded.1 (FastState.ofReference entry.1) 0).1
  rw [show BinaryArithmetic.value encoded.1=amount from BinaryNaturalView.encode_value _] at prior
  have asBinary : result=ran.1 := value.trans prior.symm
  change (collect (n:=n) entry.2 boundary 0 result).1=(collect (n:=n) entry.2 boundary (encoded.2+ran.2) ran.1).1 ∧
    (collect (n:=n) entry.2 boundary 0 result).2 ≤ (collect (n:=n) entry.2 boundary (encoded.2+ran.2) ran.1).2
  rw [asBinary,collect_control entry.2 boundary (encoded.2+ran.2) ran.1]
  exact ⟨rfl,Nat.le_add_right _ _⟩

theorem meets_old_entry {n : ℕ} (T : ℕ) (adj : PairFlags n) (L : ℕ) (positive : 0<L) (tape : Bits) :
    let fresh := hard T adj L positive tape
    let old := GuardedIntegerRoundingWork.hard T adj L tape
    fresh.1=old.1 ∧ fresh.2 ≤ old.2 := by
  let words := boundaryWords n L T
  let entry := prepare (GraphRelaxationRefinement.matrix adj) words.dimension words.level words.trials tape
  let amount := instructionBound n L (preparedCells n L T+1) T.bits+1
  exact compare_collect n entry words.paid amount _ (PaidTotalRawGraphExecution.run_eq entry.1 (input adj L T tape) positive)

theorem hard_value {n : ℕ} (T : ℕ) (adj : PairFlags n) (L : ℕ) (positive : 0<L) (tape : Bits) :
    (hard T adj L positive tape).1=PhysicalIntegerRounding.hardRun T adj L tape :=
  (meets_old_entry T adj L positive tape).1.trans (GuardedIntegerRoundingWork.hard_value T adj L tape)

theorem hard_paid {n T L : ℕ} (adj : PairFlags n) (positive : 0<L) (tape : Bits) :
    (hard T adj L positive tape).2 ≤ GuardedIntegerRoundingWork.budget n L T :=
  (meets_old_entry T adj L positive tape).2.trans (GuardedIntegerRoundingWork.hard_paid adj tape)

end DirectedFlowCutGap.GuardedFuelFreeRounding
