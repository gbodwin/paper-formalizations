import DirectedFlowCutGap.PaidTotalRawGraphExecution
import DirectedFlowCutGap.CachedHeapBuild
import DirectedFlowCutGap.CachedWalkAddresses
import DirectedFlowCutGap.OriginalGraphCostEnvelope

/-! Polynomial extent and copying bounds for the initial cache fold and the
actual cached packed rounding steps on every literal tape. -/
namespace DirectedFlowCutGap.PackedStoragePolynomial

open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal
open RetainedGridState (PairFlags)
open RawGraphControllerProgram (program instructionBound)
open CachedReferenceExecution (FastState)
open OriginalGraphCostEnvelope (preparedCells packedCost)

private theorem prepared_le (n L T : ℕ) : preparedCells n L T+1 ≤ packedCost n L T := by
  let H := preparedCells n L T
  have pow : H≤H^3 := Nat.le_self_pow (by decide) _
  unfold packedCost
  dsimp only
  change H+1 ≤ 64*H^3+16+_
  omega

private theorem instructions_le (n L T : ℕ) :
    instructionBound n L (preparedCells n L T+1) T.bits ≤ packedCost n L T := by
  let H := preparedCells n L T
  let t := instructionBound n L (H+1) T.bits
  let g := GuardedReferenceExecution.guardCost 26704
  have unit : 1≤g := by decide
  have inside : (t+1)*g ≤ packedCost n L T := by
    unfold packedCost RawGraphControllerProgram.chargeBound
    dsimp only
    exact (Nat.le_add_left _ _).trans (Nat.le_add_left _ _)
  have lower : t ≤ (t+1)*g := by
    calc
      t ≤ t+1 := Nat.le_succ _
      _ = (t+1)*1 := (Nat.mul_one _).symm
      _ ≤ _ := Nat.mul_le_mul_left _ unit
  exact lower.trans inside

/-- Place both stages after the supplied input cells. Each address fits the
width computed from the total fresh extent of the build and the walk. -/
theorem combined_layout {C buildCells buildCopies steps runCells runCopies : ℕ}
    {p : Program C} {initial : BitState C} {stop : FastState C}
    (built : CachedHeapBuild.Build CachedReferenceHeap.empty initial.heap
      (FastState.ofReference initial).store buildCells buildCopies)
    (walked : PaidCacheTrace.Walk p (FastState.ofReference initial) steps runCells runCopies stop)
    (start : ℕ) :
    let setup := CachedHeapBuild.placements CachedReferenceHeap.empty initial.heap start
    ∃ blocks, PaidCacheTrace.Layout p (FastState.ofReference initial) setup.1 stop
        (start+buildCells+runCells) blocks ∧
      ∀ block ∈ setup.2++blocks, ∀ offset<block.2,
        (block.1+offset).size ≤ (start+buildCells+runCells).size := by
  let setup := CachedHeapBuild.placements CachedReferenceHeap.empty initial.heap start
  obtain ⟨setupEnd,setupBound⟩ := built.placement start
  change setup.1=start+buildCells at setupEnd
  obtain ⟨blocks,layout,runBound⟩ := walked.layout setup.1
  refine ⟨blocks,?_,?_⟩
  · rw [← setupEnd]
    exact layout
  · intro block member offset valid
    apply Nat.size_le_size
    rcases List.mem_append.mp member with first|later
    · exact (setupBound block first offset valid).2.le.trans (Nat.le_add_right _ _)
    · have bound := (runBound block later offset valid).2.le
      exact bound.trans_eq (congrArg (·+runCells) setupEnd)

open Polynomial in
/-- These are structural copy and allocation counts for the packed rounding
stage, including its initial conversion to the cache. The tape is read only
as requested. No charge for an outer solver is inferred here. -/
theorem polynomial : ∃ fresh operations : Polynomial ℕ,
    ∀ (n L T : ℕ) (adj : PairFlags n) (initial : BitState 26704)
      (data : RawGraphControllerLaw.Input (L:=L) adj T.bits (preparedCells n L T+1) (preparedCells n L T) initial)
      (positive : 0<L), L≤n →
    ∃ buildCells buildCopies steps runCells runCopies stop,
      CachedHeapBuild.Build CachedReferenceHeap.empty initial.heap (FastState.ofReference initial).store buildCells buildCopies ∧
      PaidCacheTrace.Walk program (FastState.ofReference initial) steps runCells runCopies stop ∧
      buildCells+runCells≤fresh.eval (n+T) ∧ buildCopies+runCopies≤operations.eval (n+T) ∧
      match (PaidTotalRawGraphExecution.run initial data positive).1 with
      | none => TotalGuardedPackedExecution.blocked program stop
      | some final => final=stop ∧ program stop.pc=.halt := by
  obtain ⟨p,model⟩ := OriginalGraphCostEnvelope.bounded_trials_polynomial
  refine ⟨p*(9*p+22),p*(36*p+46),?_⟩
  intro n L T adj initial data positive inside
  let H := preparedCells n L T+1
  let P := p.eval (n+T)
  have cost : packedCost n L T≤P := model n L T inside
  have extent : H≤P := (prepared_le n L T).trans cost
  have size : initial.heap.length≤H := by
    have shape := data.bounded.1
    unfold State.records at shape
    omega
  obtain ⟨bc,bp,build,buildSpace,buildWork⟩ := CachedHeapBuild.original_build initial
  obtain ⟨steps,maxSteps,rc,rp,stop,walk,_,runSpace,runWork,observed⟩ :=
    PaidTotalRawGraphExecution.storage_traffic initial data positive
  have count : steps≤P := maxSteps.trans ((instructions_le n L T).trans cost)
  have grown : H+steps≤2*P := by omega
  have initialCap := size.trans extent
  have Bc : bc≤P*(3*P+11) := buildSpace.trans (Nat.mul_le_mul initialCap
    (Nat.add_le_add_right (Nat.mul_le_mul_left 3 initialCap) 11))
  have Bp : bp≤P*(12*P+23) := buildWork.trans (Nat.mul_le_mul initialCap
    (Nat.add_le_add_right (Nat.mul_le_mul_left 12 initialCap) 23))
  have Rc : rc≤P*(6*P+11) := runSpace.trans (by
    rw [show 6*P=3*(2*P) by ring]
    exact Nat.mul_le_mul count (Nat.add_le_add_right (Nat.mul_le_mul_left 3 grown) 11))
  have Rp : rp≤P*(24*P+23) := runWork.trans (by
    rw [show 24*P=12*(2*P) by ring]
    exact Nat.mul_le_mul count (Nat.add_le_add_right (Nat.mul_le_mul_left 12 grown) 23))
  refine ⟨bc,bp,steps,rc,rp,stop,build,walk,?_,?_,?_⟩
  · simp only [eval_mul,eval_add,eval_ofNat]
    exact (Nat.add_le_add Bc Rc).trans_eq (by unfold P; ring)
  · simp only [eval_mul,eval_add,eval_ofNat]
    exact (Nat.add_le_add Bp Rp).trans_eq (by unfold P; ring)
  · cases reached : (PaidTotalRawGraphExecution.run initial data positive).1 <;>
      simpa only [reached] using observed

end DirectedFlowCutGap.PackedStoragePolynomial
