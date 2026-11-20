import DirectedFlowCutGap.PhysicalSourceReadback
import DirectedFlowCutGap.VertexSourceCacheLayout

/-! Bound the modeled cache and returned-array reservations in program order.
The allocation schedule records persistent copy constructors. -/
namespace DirectedFlowCutGap.VertexSourceTerminalLayout

open BinaryArithmetic ImmutableReferenceSimulation
open CachedReferenceExecution (FastState)
open EncodedArrayStorage (Instruction allocateTrace fresh fresh_append)
open PhysicalSourceDispatch (program initial input instructionPolynomial)
open PhysicalSourceBinaryCache (evaluate)
open PhysicalCoverReader (Plan plan)
open Polynomial

theorem array_polynomial : ∃ cells copies : Polynomial ℕ,
    ∀ {n : ℕ} (D : BinaryFractionalGuesses.Input n),
      let source := (BinarySourceSerialization.run D).1
      let out := (evaluate D source (BinarySourceSerialization.run_value D)).1.1
      let returned := plan (BinaryFractionalGuesses.solveInput D).1
      ∃ cacheCode : List (Instruction Unit),
        (PhysicalSourceReadback.runWithBitCharges D).1.1 = some returned ∧
        let code := cacheCode ++ BinaryCoverReadback.terminalArrayCode returned
        fresh code ≤ cells.eval source.length ∧ code.length ≤ copies.eval source.length ∧
        ∀ start : ℕ,
          let cache := allocateTrace start cacheCode
          let terminal := allocateTrace cache.1 (BinaryCoverReadback.terminalArrayCode returned)
          let placed := allocateTrace start code
          let width := (start+cells.eval source.length).size
          let binary := BinaryAllocationTrace.allocate start.bits (code.map BinaryAllocationTrace.reservation)
          PaidCacheTrace.Layout program (FastState.ofReference (initial source)) start out cache.1 cache.2 ∧
          placed=(terminal.1,cache.2++terminal.2) ∧
          (value binary.stop,binary.blocks.map (fun (a,b) => (value a,value b)))=placed ∧
          binary.charge≤BinaryAllocationTrace.chargeBound (copies.eval source.length) width ∧
          ∀ block∈placed.2, ∀ offset<block.2, (block.1+offset).size≤width := by
  obtain ⟨cacheCells,cacheCopies,cache_layout⟩ := VertexSourceCacheLayout.array_polynomial
  let p := instructionPolynomial
  let cells := cacheCells+(p+3)*(X^2+7*X+2)
  let copies := cacheCopies+(p+3)*(2*X^2+21*X+4)
  refine ⟨cells,copies,?_⟩
  intro n D
  let source := (BinarySourceSerialization.run D).1
  have encoded : source = input D := BinarySourceSerialization.run_value D
  let out := (evaluate D source encoded).1.1
  let returned := plan (BinaryFractionalGuesses.solveInput D).1
  obtain ⟨cacheCode,cacheSpace,cacheWork,cachePlaced⟩ := cache_layout D source encoded
  obtain ⟨legacy,readback,complete,_,_⟩ := PhysicalSourceReadback.run_eq D
  have observed : (PhysicalSourceReadback.runWithBitCharges D).1.1 = some returned := by
    rw [PhysicalSourceReadback.metered_plan,complete]
    rfl
  have terminalRead : (BinaryCoverReadback.readPlanCached n out.store out.registers.d).1=some returned := by
    simpa only [PhysicalSourceReadback.runWithBitCharges,BinaryCoverReadback.readPlanWithBitCharge_value,
      source,out] using observed
  obtain ⟨terminalWork,terminalSpace⟩ := BinaryCoverReadback.terminal_array_counts terminalRead
  have width : n ≤ source.length := by
    rw [encoded]
    exact (Nat.le_succ n).trans (BinarySourceSerialization.input_dimensions D)
  have stateBound := PhysicalSourceBinaryCache.output_bounds D source encoded
  have heapBound : out.store.cells.size+1 ≤ p.eval source.length+3 := by
    have count := stateBound.1
    simp only [State.records,CachedReferenceExecution.FastState.freeze,Array.length_toList,
      BinarySourceFuel.fuel_value] at count
    change out.store.cells.size+1 ≤ instructionPolynomial.eval source.length+3
    change out.store.cells.size+out.stack.length+1 ≤ 1+(instructionPolynomial.eval source.length+1) at count
    omega
  let code := cacheCode ++ BinaryCoverReadback.terminalArrayCode returned
  have cellBound : fresh code ≤ cells.eval source.length := by
    simp only [code,fresh_append,cells,eval_add,eval_mul,eval_pow,eval_ofNat,eval_X]
    exact Nat.add_le_add cacheSpace (terminalSpace.trans (by gcongr))
  have copyBound : code.length ≤ copies.eval source.length := by
    simp only [code,List.length_append,copies,eval_add,eval_mul,eval_pow,eval_ofNat,eval_X]
    exact Nat.add_le_add cacheWork (terminalWork.trans (by gcongr))
  refine ⟨cacheCode,observed,cellBound,copyBound,fun start => ?_⟩
  obtain ⟨same,paid,widths⟩ := PackedArrayReservations.binary_layout code start
  have fits : (start+fresh code).size≤(start+cells.eval source.length).size :=
    Nat.size_le_size (Nat.add_le_add_left cellBound start)
  exact ⟨(cachePlaced start).1,PackedArraySchedule.allocation_append _ _ _,same,
    paid.trans (by unfold BinaryAllocationTrace.chargeBound; gcongr),
    fun block member offset inside => (widths block member offset inside).trans fits⟩

end DirectedFlowCutGap.VertexSourceTerminalLayout
