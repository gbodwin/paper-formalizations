import DirectedFlowCutGap.BinarySourceSerialization
import DirectedFlowCutGap.BinarySourceFuel
import DirectedFlowCutGap.BinaryCoverReadback

/-!
# Serialized source, exact terminal plans, and phase charges

The input words are framed and the dispatch fuel is evaluated by binary
arithmetic before the cached evaluator starts. At halt the reader traverses
the actual terminal store, validates the fractions, and decodes the reached
rows or witness. The returned readback charge includes this source setup.
-/

namespace DirectedFlowCutGap.PhysicalSourceReadback

open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal
open PhysicalCoverReader

def planBound {R : Type*} [Semiring R] (H B : R) : R :=
  BinaryCoverReadback.budget H B+BinarySourceSerialization.budget B+BinarySourceFuel.budget B

theorem planBound_mono {H B H' B' : ℕ} (hH : H ≤ H') (hB : B ≤ B') :
    planBound H B ≤ planBound H' B' := by
  unfold planBound
  exact Nat.add_le_add (Nat.add_le_add (BinaryCoverReadback.budget_mono hH hB)
    (BinarySourceSerialization.budget_mono hB)) (BinarySourceFuel.budget_mono hB)

open Polynomial in
theorem planBound_eval (H B : Polynomial ℕ) (x : ℕ) :
    (planBound H B).eval x=planBound (H.eval x) (B.eval x) := by
  simp only [planBound,eval_add,BinaryCoverReadback.budget_eval,BinarySourceSerialization.budget_eval,
    BinarySourceFuel.budget_eval]

theorem terminal_charge {C : ℕ} (n : ℕ) (s : BitState C) {H B : ℕ} (hn : n ≤ B) (hs : s.Bounded H B) :
    (BinaryCoverReadback.readPlan n s.heap s.registers.d).2 ≤ BinaryCoverReadback.budget H B := by
  have hH : s.heap.length ≤ H := by
    have hrecords := hs.1
    unfold State.records at hrecords
    omega
  exact (BinaryCoverReadback.readPlan_charge n hn hs.2.2.1 (Registers.get_all hs.2.2.2.1 .r3)).trans
    (BinaryCoverReadback.budget_mono hH le_rfl)

private def readout {C : ℕ} (n : ℕ) (out : BitState C) (physical setup : ℕ) : Option (Plan n × ℕ × ℕ) :=
  let result := BinaryCoverReadback.readPlan n out.heap out.registers.d
  result.1.map fun p => (p,physical,result.2+setup)

def run {n : ℕ} (D : BinaryFractionalGuesses.Input n) : Option (Plan n × ℕ × ℕ) :=
  let input := BinarySourceSerialization.run D
  let fuel := BinarySourceFuel.compute input.1.length
  let initial := CachedReferenceExecution.FastState.ofReference (PhysicalSourceDispatch.initial input.1)
  (CachedReferenceExecution.execute PhysicalSourceDispatch.program fuel.1 initial 0).bind fun (out,physical) =>
    let result := BinaryCoverReadback.readPlanCached n out.store out.registers.d
    result.1.map fun p => (p,physical,result.2+input.2+fuel.2)

theorem run_reference {n : ℕ} (D : BinaryFractionalGuesses.Input n) :
    let source := PhysicalSourceDispatch.input D
    let fuel := BinarySourceFuel.compute source.length
    run D = (PhysicalCoverExecution.execute PhysicalSourceDispatch.program fuel.1
      (PhysicalSourceDispatch.initial source) 0).bind (fun (out,physical) =>
        readout n out physical ((BinarySourceSerialization.run D).2+fuel.2)) := by
  dsimp only
  rw [← PhysicalCoverExecution.executeCached_eq]
  simp only [run,PhysicalCoverExecution.executeCached,BinarySourceSerialization.run_value]
  generalize CachedReferenceExecution.execute PhysicalSourceDispatch.program
    (BinarySourceFuel.compute (PhysicalSourceDispatch.input D).length).1
    (CachedReferenceExecution.FastState.ofReference
      (PhysicalSourceDispatch.initial (PhysicalSourceDispatch.input D))) 0 = result
  cases result with
  | none => rfl
  | some out =>
    rcases out with ⟨state, paid⟩
    simp only [Option.bind_some,Option.map_some,BinaryCoverReadback.readPlanCached_eq,readout,
      CachedReferenceExecution.FastState.freeze,Nat.add_assoc]

theorem run_eq {n : ℕ} (D : BinaryFractionalGuesses.Input n) :
    let size := (PhysicalSourceDispatch.input D).length
    let bound := PhysicalSourceDispatch.instructionPolynomial.eval size
    ∃ physical readback,
      run D = some (plan (BinaryFractionalGuesses.solveInput D).1,physical,readback) ∧
      physical ≤ PhysicalSourceDispatch.paidPolynomial.eval size ∧
      readback ≤ planBound (1+bound) bound := by
  dsimp only
  obtain ⟨k,charge,out,hk,trace,hhalt,_,hpaid,hresult⟩ := PhysicalSourceDispatch.bit_trace D
  let L := (PhysicalSourceDispatch.input D).length
  let bound := PhysicalSourceDispatch.instructionPolynomial.eval L
  let source := BinarySourceSerialization.run D
  let fuel := BinarySourceFuel.compute L
  let readCost := (BinaryCoverReadback.readPlan n out.heap out.registers.d).2
  let paid := charge+(attempt PhysicalSourceDispatch.program out).operations
  have hstart : (PhysicalSourceDispatch.initial (PhysicalSourceDispatch.input D)).Bounded 1 0 := by
    simp [PhysicalSourceDispatch.initial,State.Bounded,State.records,Registers.All,Heap.Bounded]
  have fuelBound : fuel.1=bound+1 := BinarySourceFuel.fuel_value _
  have enough : k ≤ bound := hk.trans (PhysicalSourceDispatch.steps_polynomial D)
  have hs := reached_bounded trace hstart enough
  have hL : n+1 ≤ L := BinarySourceSerialization.input_dimensions D
  have Lbound : L ≤ bound := BinarySourceFuel.length_le _
  have hread := terminal_charge n out (show n ≤ bound by omega)
    (show out.Bounded (1+bound) bound by simpa only [Nat.zero_add] using hs)
  have he := PhysicalCoverExecution.execute_eq trace hhalt fuel.1 0 (by omega)
  have hr : (BinaryCoverReadback.readPlan n out.heap out.registers.d).1=
      some (plan (BinaryFractionalGuesses.solveInput D).1) := by
    rw [BinaryCoverReadback.readPlan_value,PhysicalCoverAccess.readPlan_value]
    exact PhysicalCoverReader.readPlan_eq hresult
  refine ⟨paid,readCost+(source.2+fuel.2),?_,hpaid.trans (PhysicalSourceDispatch.paidBound_polynomial D),?_⟩
  · rw [run_reference]
    simp only
    change (PhysicalCoverExecution.execute _ fuel.1 _ 0).bind _ = _
    simp only [he,Option.bind_some,Nat.zero_add,readout,hr,Option.map_some,paid,readCost,source]
    rfl
  · rw [← Nat.add_assoc]
    exact Nat.add_le_add (Nat.add_le_add hread
      ((BinarySourceSerialization.run_paid D).trans (BinarySourceSerialization.budget_mono Lbound)))
      (BinarySourceFuel.compute_paid (by omega))

end DirectedFlowCutGap.PhysicalSourceReadback
