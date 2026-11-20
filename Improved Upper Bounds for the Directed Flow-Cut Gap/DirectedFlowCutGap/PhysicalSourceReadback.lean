import DirectedFlowCutGap.BinarySourceSerialization
import DirectedFlowCutGap.BinarySourceFuel
import DirectedFlowCutGap.BinaryCoverReadback
import DirectedFlowCutGap.PhysicalSourceBinaryCache

/-!
# Serialized source, exact terminal plans, and phase charges

The original words are framed and the earlier source setup charge is
retained. The binary cached evaluator uses the termination proof for the
actual source dispatcher. At halt the reader traverses the returned store,
validates the fractions, and decodes the reached rows or witness.
-/

namespace DirectedFlowCutGap.PhysicalSourceReadback

open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal
open PhysicalCoverReader
open PhysicalCoverAccess (Read)

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

private def readoutCached {C : ℕ} (n : ℕ) (out : CachedReferenceExecution.FastState C)
    (physical setup : ℕ) : Option (Plan n × ℕ × ℕ) :=
  let read := BinaryCoverReadback.readPlanCached n out.store out.registers.d
  read.1.map fun p => (p,physical,read.2+setup)

def runWithCacheCharge {n : ℕ} (D : BinaryFractionalGuesses.Input n) : Option (Plan n × ℕ × ℕ) × ℕ :=
  let input := BinarySourceSerialization.run D
  let setup := input.2+(BinarySourceFuel.compute input.1.length).2
  let execution := PhysicalSourceBinaryCache.evaluate D input.1 (BinarySourceSerialization.run_value D)
  (readoutCached n execution.1.1 execution.1.2 setup,execution.2)

def run {n : ℕ} (D : BinaryFractionalGuesses.Input n) : Option (Plan n × ℕ × ℕ) :=
  (runWithCacheCharge D).1

/-- Count the source serialization, cached execution and terminal parser on one run. -/
def runWithBitCharges {n : ℕ} (D : BinaryFractionalGuesses.Input n) : Read (Plan n) × ℕ :=
  let input := BinarySourceSerialization.run D
  let execution := PhysicalSourceBinaryCache.evaluate D input.1 (BinarySourceSerialization.run_value D)
  let out := execution.1.1
  (BinaryCoverReadback.readPlanWithBitCharge n out.store out.registers.d,execution.2+input.2)

theorem metered_plan {n : ℕ} (D : BinaryFractionalGuesses.Input n) :
    (runWithBitCharges D).1.1=(run D).map Prod.fst := by
  simp only [runWithBitCharges,run,runWithCacheCharge,readoutCached,BinaryCoverReadback.readPlanWithBitCharge_value]
  cases (BinaryCoverReadback.readPlanCached n
    (PhysicalSourceBinaryCache.evaluate D (BinarySourceSerialization.run D).1
      (BinarySourceSerialization.run_value D)).1.1.store
    (PhysicalSourceBinaryCache.evaluate D (BinarySourceSerialization.run D).1
      (BinarySourceSerialization.run_value D)).1.1.registers.d).1 <;> rfl

private theorem bitCharges_bound {n : ℕ} (D : BinaryFractionalGuesses.Input n) :
    let fuel := (BinarySourceFuel.compute (PhysicalSourceDispatch.input D).length).1
    (runWithBitCharges D).1.2 + (runWithBitCharges D).2 ≤
      BinaryCoverReadback.measuredBudget (1+fuel) fuel +
        (PhysicalSourceBinaryCache.budget fuel + BinarySourceSerialization.budget (PhysicalSourceDispatch.input D).length) := by
  let input := BinarySourceSerialization.run D
  have same : input.1 = PhysicalSourceDispatch.input D := BinarySourceSerialization.run_value D
  let fuel := (BinarySourceFuel.compute input.1.length).1
  let out := (PhysicalSourceBinaryCache.evaluate D input.1 same).1.1
  have size : out.freeze.Bounded (1+fuel) fuel := PhysicalSourceBinaryCache.output_bounds D input.1 same
  have entries := size.1
  have count : out.store.cells.size ≤ 1+fuel := by
    simp only [State.records,CachedReferenceExecution.FastState.freeze,Array.length_toList] at entries
    omega
  have enough : n ≤ fuel := by
    have encoded : n+1 ≤ (PhysicalSourceDispatch.input D).length := BinarySourceSerialization.input_dimensions D
    have length : n ≤ input.1.length := by
      rw [same]
      exact (Nat.le_succ n).trans encoded
    unfold fuel
    rw [BinarySourceFuel.fuel_value]
    exact length.trans ((BinarySourceFuel.length_le _).trans (Nat.le_succ _))
  have terminal := BinaryCoverReadback.readPlanWithBitCharge_paid n out.store out.registers.d enough
    size.2.2.1 (Registers.get_all size.2.2.2.1 .r3)
  have control := PhysicalSourceBinaryCache.paid D input.1 same
  have framing := BinarySourceSerialization.run_paid D
  have summed := Nat.add_le_add (terminal.trans (BinaryCoverReadback.measuredBudget_mono count le_rfl))
    (Nat.add_le_add control framing)
  simpa only [runWithBitCharges,out,fuel,same,input,BinarySourceSerialization.run_value] using summed

open Polynomial OriginalGraphCostEnvelope in
theorem bitCharges_polynomial : ∃ p : Polynomial ℕ, ∀ {n : ℕ} (D : BinaryFractionalGuesses.Input n),
    (runWithBitCharges D).1.2 + (runWithBitCharges D).2 ≤ p.eval (PhysicalSourceDispatch.input D).length := by
  let fuel (length : ℕ) := (BinarySourceFuel.compute length).1
  have fuelFits : Covered (fun x : ℕ => x) fuel := by
    refine ⟨PhysicalSourceDispatch.instructionPolynomial+1, fun x => ?_⟩
    rw [eval_add,eval_one,show fuel x=_ from BinarySourceFuel.fuel_value x]
  have serialization : Covered (fun length : ℕ => length) (fun length => BinarySourceSerialization.budget length) := by
    refine ⟨BinarySourceSerialization.budget X, fun length => ?_⟩
    rw [BinarySourceSerialization.budget_eval, eval_X]
  have fits : Covered (fun x : ℕ => x) (fun x =>
      BinaryCoverReadback.measuredBudget (1+fuel x) (fuel x)+
        (PhysicalSourceBinaryCache.budget (fuel x)+BinarySourceSerialization.budget x)) := by
    cover_arithmetic
  obtain ⟨p, cap⟩ := fits
  exact ⟨p,fun D => (bitCharges_bound D).trans (cap (PhysicalSourceDispatch.input D).length)⟩

private theorem run_cached {n : ℕ} (D : BinaryFractionalGuesses.Input n) :
    let input := BinarySourceSerialization.run D
    let setup := input.2+(BinarySourceFuel.compute input.1.length).2
    run D = (PhysicalSourceBinaryCache.reference input.1).bind
      (fun (out, paid) => readoutCached n out paid setup) := by
  let input := BinarySourceSerialization.run D
  let execution := PhysicalSourceBinaryCache.evaluate D input.1 (BinarySourceSerialization.run_value D)
  have exactRun : some execution.1 = PhysicalSourceBinaryCache.reference input.1 :=
    PhysicalSourceBinaryCache.value_eq D input.1 (BinarySourceSerialization.run_value D)
  unfold run runWithCacheCharge
  dsimp only
  rw [← exactRun]
  rfl

open Polynomial in
theorem cache_polynomial : ∃ p : Polynomial ℕ, ∀ {n : ℕ} (D : BinaryFractionalGuesses.Input n),
    (runWithCacheCharge D).2 ≤ p.eval (PhysicalSourceDispatch.input D).length := by
  obtain ⟨p, covered⟩ := PhysicalSourceBinaryCache.polynomial
  refine ⟨p,fun D => ?_⟩
  have cap := covered D (BinarySourceSerialization.run D).1 (BinarySourceSerialization.run_value D)
  simpa only [runWithCacheCharge,BinarySourceSerialization.run_value] using cap

theorem run_reference {n : ℕ} (D : BinaryFractionalGuesses.Input n) :
    let source := PhysicalSourceDispatch.input D
    let fuel := BinarySourceFuel.compute source.length
    run D = (PhysicalCoverExecution.execute PhysicalSourceDispatch.program fuel.1
      (PhysicalSourceDispatch.initial source) 0).bind (fun (out,physical) =>
        readout n out physical ((BinarySourceSerialization.run D).2+fuel.2)) := by
  dsimp only
  rw [run_cached, ← PhysicalCoverExecution.executeCached_eq]
  simp only [PhysicalSourceBinaryCache.reference,PhysicalCoverExecution.executeCached,
    BinarySourceSerialization.run_value]
  generalize CachedReferenceExecution.execute PhysicalSourceDispatch.program
    (BinarySourceFuel.compute (PhysicalSourceDispatch.input D).length).1
    (CachedReferenceExecution.FastState.ofReference
      (PhysicalSourceDispatch.initial (PhysicalSourceDispatch.input D))) 0 = result
  cases result with
  | none => rfl
  | some out =>
    rcases out with ⟨state, paid⟩
    simp only [Option.bind_some,Option.map_some,BinaryCoverReadback.readPlanCached_eq,readout,readoutCached,
      CachedReferenceExecution.FastState.freeze]

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
