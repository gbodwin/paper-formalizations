import DirectedFlowCutGap.PhysicalSourceDispatch
import DirectedFlowCutGap.PhysicalCoverAccess

/-!
# Exact terminal rows and their lookup charge

The cached physical evaluator returns the actual terminal store. The
reader traverses that store using binary pointers and charges each
reference lookup. The charge bound covers both source dispatch and
terminal lookups. Typed conversion and rounding have their own costs.
-/

namespace DirectedFlowCutGap.PhysicalSourceReadback

open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal
open PhysicalCoverReader PhysicalCoverAccess

private theorem planBound_mono {H B H' B' : ℕ} (hH : H ≤ H') (hB : B ≤ B') :
    planBound H B ≤ planBound H' B' := by
  unfold planBound bestBound fractionBound wordBound cellBound
  gcongr

theorem terminal_charge {C : ℕ} (n : ℕ) (s : BitState C) {H B : ℕ} (hs : s.Bounded H B) :
    (PhysicalCoverAccess.readPlan n s.heap s.registers.d).2 ≤ planBound H B := by
  have hH : s.heap.length ≤ H := by
    have hrecords := hs.1
    unfold State.records at hrecords
    omega
  exact (readPlan_charge n hs.2.2.1 (Registers.get_all hs.2.2.2.1 .r3)).trans
    (planBound_mono hH le_rfl)

def run {n : ℕ} (D : BinaryFractionalGuesses.Input n) :
    Option (Plan n × ℕ × ℕ) :=
  let args := PhysicalSourceDispatch.input D
  (PhysicalCoverExecution.executeCached PhysicalSourceDispatch.program
    (PhysicalSourceDispatch.steps D + 1) (PhysicalSourceDispatch.initial args) 0).bind
      fun (out, physical) =>
        let result := PhysicalCoverAccess.readPlan n out.heap out.registers.d
        result.1.map fun p => (p, physical, result.2)

theorem run_eq {n : ℕ} (D : BinaryFractionalGuesses.Input n) :
    let size := (PhysicalSourceDispatch.input D).length
    let bound := PhysicalSourceDispatch.instructionPolynomial.eval size
    ∃ physical lookups,
      run D = some (plan (BinaryFractionalGuesses.solveInput D).1, physical, lookups) ∧
      physical ≤ PhysicalSourceDispatch.paidPolynomial.eval size ∧
      lookups ≤ planBound (1 + bound) bound := by
  dsimp only
  obtain ⟨k, charge, out, hk, trace, hhalt, _, hpaid, hresult⟩ := PhysicalSourceDispatch.bit_trace D
  let lookupCost := (PhysicalCoverAccess.readPlan n out.heap out.registers.d).2
  let paid := charge + (attempt PhysicalSourceDispatch.program out).operations
  have hstart : (PhysicalSourceDispatch.initial (PhysicalSourceDispatch.input D)).Bounded 1 0 := by
    simp [PhysicalSourceDispatch.initial, State.Bounded, State.records, Registers.All, Heap.Bounded]
  have hs := reached_bounded trace hstart (hk.trans (PhysicalSourceDispatch.steps_polynomial D))
  have hlook := terminal_charge n out hs
  have he := PhysicalCoverExecution.execute_eq trace hhalt (PhysicalSourceDispatch.steps D + 1) 0 (by omega)
  have hr : (PhysicalCoverAccess.readPlan n out.heap out.registers.d).1 =
      some (plan (BinaryFractionalGuesses.solveInput D).1) := by
    rw [readPlan_value]
    exact PhysicalCoverReader.readPlan_eq hresult
  refine ⟨paid, lookupCost, ?_, hpaid.trans (PhysicalSourceDispatch.paidBound_polynomial D), ?_⟩
  · simp only [run, PhysicalCoverExecution.executeCached_eq, he, Option.bind_some, Nat.zero_add,
      hr, Option.map_some, paid, lookupCost]
  · simpa only [lookupCost, Nat.zero_add] using hlook

end DirectedFlowCutGap.PhysicalSourceReadback
