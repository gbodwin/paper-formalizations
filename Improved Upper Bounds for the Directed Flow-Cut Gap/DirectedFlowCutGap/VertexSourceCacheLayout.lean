import DirectedFlowCutGap.PhysicalSourceBinaryCache
import DirectedFlowCutGap.CompleteCacheTraffic
import DirectedFlowCutGap.PackedArrayReservations

/-! The completed original vertex source supplies every request bit. This
identifies the cached dispatcher's exact modeled array walk and extent. -/
namespace DirectedFlowCutGap.VertexSourceCacheLayout

open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal
open CachedReferenceExecution (FastState)
open PhysicalSourceDispatch (program initial input instructionPolynomial)
open PhysicalSourceBinaryCache (evaluate reference value_eq)

theorem walk {n : ℕ} (D : BinaryFractionalGuesses.Input n) (source : Bits) (encoded : source = input D) :
    ∃ steps ≤ instructionPolynomial.eval source.length, ∃ cells copies,
      PaidCacheTrace.Walk program (FastState.ofReference (initial source)) steps cells copies
        (evaluate D source encoded).1.1 := by
  subst source
  let source := input D
  let start := FastState.ofReference (initial source)
  let finish := evaluate D source rfl
  let fuel := (BinarySourceFuel.compute source.length).1
  obtain ⟨steps, cost, out, fits, trace, stopped, _, _, _⟩ := PhysicalSourceDispatch.bit_trace D
  have within := fits.trans (PhysicalSourceDispatch.steps_polynomial D)
  have requested : GuardedReferenceExecution.requestCount (source.map Event.request) ≤ (initial source).source.length := by
    rw [GuardedReferenceExecution.count_reads]
    rfl
  obtain ⟨cells,copies,done,history,endState⟩ := CompleteCacheTraffic.complete_walk trace requested start
    (CachedReferenceExecution.freeze_ofReference _)
  have halt : tick program done.freeze = none := by
    rw [endState,← ImmutableReferenceTerminal.attempt_result]
    exact stopped
  have enough : steps < fuel := by
    rw [show fuel=instructionPolynomial.eval source.length+1 from BinarySourceFuel.fuel_value _]
    exact Nat.lt_succ_of_le within
  obtain ⟨paid, actual⟩ := CompleteCacheTraffic.execute_walk history halt fuel 0 enough
  have observed : some finish.1 = reference source := value_eq D source rfl
  change reference source = some (done,paid) at actual
  rw [actual] at observed
  have stateEq : finish.1.1=done := congrArg Prod.fst (Option.some.inj observed)
  change ∃ steps ≤ instructionPolynomial.eval source.length, ∃ cells copies,
    PaidCacheTrace.Walk program start steps cells copies finish.1.1
  rw [stateEq]
  exact ⟨steps, within, cells, copies, history⟩

open Polynomial EncodedArrayStorage in
theorem array_polynomial : ∃ cells copies : Polynomial ℕ,
    ∀ {n : ℕ} (D : BinaryFractionalGuesses.Input n) (source : Bits) (encoded : source = input D),
    ∃ code : List (EncodedArrayStorage.Instruction Unit),
      fresh code ≤ cells.eval source.length ∧ code.length ≤ copies.eval source.length ∧
      ∀ start : ℕ,
        let placed := allocateTrace start code
        let width := (start+cells.eval source.length).size
        let binary := BinaryAllocationTrace.allocate start.bits (code.map BinaryAllocationTrace.reservation)
        PaidCacheTrace.Layout program (FastState.ofReference (initial source)) start
          (evaluate D source encoded).1.1 placed.1 placed.2 ∧
        (value binary.stop,binary.blocks.map (fun (a,b) => (value a,value b)))=placed ∧
        binary.charge≤BinaryAllocationTrace.chargeBound (copies.eval source.length) width ∧
        ∀ block∈placed.2, ∀ offset<block.2, (block.1+offset).size≤width := by
  let p := instructionPolynomial
  let cells : Polynomial ℕ := p*(3*(1+p)+11)
  let copies : Polynomial ℕ := p*(12*(1+p)+23)
  refine ⟨cells,copies,?_⟩
  intro n D source encoded
  let state := FastState.ofReference (initial source)
  have shape : state.freeze.Bounded 1 0 := by
    rw [show state.freeze=initial source from CachedReferenceExecution.freeze_ofReference _]
    simp [initial,State.Bounded,State.records,Registers.All,Heap.Bounded]
  obtain ⟨steps,within,allocated,counted,history⟩ := walk D source encoded
  obtain ⟨_,space,work⟩ := history.bounded shape
  obtain ⟨code,length,extent,placed⟩ := PackedArraySchedule.walk_schedule history
  have cellBound : fresh code≤cells.eval source.length := by
    simp only [extent,cells,eval_add,eval_one,eval_ofNat,eval_mul]
    exact space.trans (by gcongr)
  have copyBound : code.length≤copies.eval source.length := by
    simp only [length,copies,eval_add,eval_one,eval_ofNat,eval_mul]
    exact work.trans (by gcongr)
  refine ⟨code,cellBound,copyBound,fun start => ?_⟩
  obtain ⟨same,paid,widths⟩ := PackedArrayReservations.binary_layout code start
  have fits : (start+fresh code).size≤(start+cells.eval source.length).size :=
    Nat.size_le_size (Nat.add_le_add_left cellBound start)
  exact ⟨placed start,same,paid.trans (by unfold BinaryAllocationTrace.chargeBound; gcongr),
    fun block member offset inside => (widths block member offset inside).trans fits⟩

end DirectedFlowCutGap.VertexSourceCacheLayout
