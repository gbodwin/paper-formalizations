import DirectedFlowCutGap.PhysicalCoverReader

/-!
# Executing the recovered fractional dispatcher

This evaluator uses the physical terminal-inclusive dispatcher. It reads
the actual terminal heap into the plan used by rounding.
-/

namespace DirectedFlowCutGap.PhysicalCoverExecution

open ImmutableReferenceSimulation ImmutableReferenceTerminal EncodedSequenceAccess
open PhysicalCoverReader

def execute {C : ℕ} (p : Program C) : ℕ → BitState C → ℕ → Option (BitState C × ℕ)
  | 0, _, _ => none
  | fuel + 1, s, paid =>
    let step := attempt p s
    match step.result with
    | none => some (s, paid + step.operations)
    | some r => execute p fuel r.state (paid + step.operations)

theorem execute_eq {C k q : ℕ} {p : Program C} {s u : BitState C} {events : List Event}
    (h : Run p k q s events u) (halted : (attempt p u).result = none)
    (fuel paid : ℕ) (hf : k < fuel) :
    execute p fuel s paid = some (u, paid + q + (attempt p u).operations) := by
  induction h generalizing fuel paid with
  | done s =>
    cases fuel with
    | zero => omega
    | succ fuel => simp [execute, halted]
  | @step s u r k q events hstep hr ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have ht : (attempt p s).result = some r := (attempt_result p s).trans hstep
      simp only [execute, ht, success_cost ht]
      simpa only [Nat.add_assoc] using ih halted fuel (paid + r.cost) (by omega)

private theorem attempt_pos {C : ℕ} (p : Program C) (s : BitState C) :
    0 < (attempt p s).operations := by
  cases h : p s.pc with
  | halt => simp [attempt, h, stopped, controlCost]
  | move => simp [attempt, h, success, controlCost]
  | make => simp [attempt, h, success, allocate, controlCost]
  | branch src n f t pair =>
    simp only [attempt, h]
    cases (lookup (copyBits (s.registers.get src)).1 s.heap).1 <;>
      simp [success, stopped, controlCost]
  | field dst src right pc =>
    simp only [attempt, h]
    cases (lookup (copyBits (s.registers.get src)).1 s.heap).1 with
    | none => simp [stopped, controlCost]
    | some c => cases c <;> simp [success, stopped, controlCost]
  | call => simp [attempt, h, success, controlCost]
  | ret =>
    simp only [attempt, h]
    cases s.stack <;> simp [success, stopped, controlCost]
  | request => simp [attempt, h, success, allocate, controlCost]
  | emit src pc =>
    simp only [attempt, h]
    cases (lookup (copyBits (s.registers.get src)).1 s.heap).1 with
    | none => simp [stopped, controlCost]
    | some c => cases c <;> simp [success, stopped, controlCost]

private theorem run_length_le_charge {C k q : ℕ} {p : Program C} {s u : BitState C}
    {events : List Event} (h : Run p k q s events u) : k ≤ q := by
  induction h with
  | done => rfl
  | @step s u r k q events hstep _ ih =>
    have ht : (attempt p s).result = some r := (attempt_result p s).trans hstep
    have hq : 0 < r.cost := success_cost ht ▸ attempt_pos p s
    omega

def budget {n : ℕ} (D : BinaryFractionalGuesses.Input n) : ℕ :=
  let H := OriginalStoreInitial.heapCells D.adjacency D.costs D.demands
  OriginalStoreInitial.preparationBound D.adjacency D.costs D.demands +
    completeBound 13320 (H + 1) H (FinalDispatch.inputBound D.adjacency D.costs D.demands)

/-- The charge field counts typed preparation and the physical dispatcher,
including the final paid stop. The heap reader is executed afterward. -/
def run {n : ℕ} (D : BinaryFractionalGuesses.Input n) : Option (Plan n × ℕ) := do
  let start := OriginalStoreInitial.prepare D.adjacency D.costs D.demands
  let (out, paid) ← execute FinalDispatch.program (budget D + 1) start.1 start.2
  let result := eraseState out
  let p ← readPlan n result.heap result.registers.d
  return (p, paid)

theorem run_eq {n : ℕ} (D : BinaryFractionalGuesses.Input n) :
    ∃ paid, run D = some (plan (BinaryFractionalGuesses.solveInput D).1, paid) ∧ paid ≤ budget D := by
  cases D with
  | mk adjacency demands costs =>
    obtain ⟨_, k, charge, out, _, hr, houtput, _, _, _, _, _, _, _, _, _, _, _, hhalt, hb⟩ :=
      OriginalStoreDispatch.solve_original_bit adjacency costs demands
    let D : BinaryFractionalGuesses.Input n := ⟨adjacency, demands, costs⟩
    let paid := (OriginalStoreInitial.prepare adjacency costs demands).2 +
      charge + (attempt FinalDispatch.program out).operations
    have hpaid : paid ≤ budget D := hb
    have hk : k ≤ charge := run_length_le_charge hr
    have hk' : k < budget D + 1 := by
      unfold paid at hpaid
      omega
    have hex := execute_eq hr hhalt (budget D + 1)
      (OriginalStoreInitial.prepare adjacency costs demands).2 hk'
    have hread := readPlan_eq houtput
    refine ⟨paid, ?_, hpaid⟩
    simp [run, D, paid, hex, hread]

theorem budget_polynomial {n : ℕ} (D : BinaryFractionalGuesses.Input n) :
    budget D ≤ OriginalStoreDispatch.totalPolynomial.eval
      (OriginalStoreInitial.inputSize D.costs D.demands) := by
  let N := OriginalStoreInitial.inputSize D.costs D.demands
  let H := OriginalStoreInitial.heapCells D.adjacency D.costs D.demands
  have hn : n ≤ N := by unfold N OriginalStoreInitial.inputSize; omega
  have hd : D.demands.length ≤ N := by unfold N OriginalStoreInitial.inputSize; omega
  have hs : LambdaRowProgram.rowBits D.costs.toList ≤ N := by
    unfold N OriginalStoreInitial.inputSize
    omega
  have hH : H ≤ 32 * N ^ 2 := OriginalStoreInitial.heapCells_bound D.adjacency D.costs D.demands
  have diagonal : OriginalStoreDispatch.diagonalPolynomial.eval N = 32 * N ^ 2 + 2 * N + 2 := by
    simp [OriginalStoreDispatch.diagonalPolynomial]
  have hphysical := FinalDispatchEnvelope.physical_le_eval D.adjacency D.costs D.demands
    (N := OriginalStoreDispatch.diagonalPolynomial.eval N) (H := H + 1) (B := H)
    (by rw [diagonal]; omega) (by rw [diagonal]; omega) (by rw [diagonal]; omega)
    (by rw [diagonal]; omega) (by rw [diagonal]; omega)
  have hprep := OriginalStoreDispatch.preparation_le_eval D.adjacency D.costs D.demands
  simp only [OriginalStoreDispatch.totalPolynomial, Polynomial.eval_add, Polynomial.eval_comp]
  exact add_le_add hprep hphysical

end DirectedFlowCutGap.PhysicalCoverExecution
