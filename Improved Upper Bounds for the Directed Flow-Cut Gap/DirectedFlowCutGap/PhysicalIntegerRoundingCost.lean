import DirectedFlowCutGap.PhysicalIntegerRounding
import DirectedFlowCutGap.OriginalGraphCostEnvelope

/-! Bound the packed controller and the actual binary cut readback. -/

namespace DirectedFlowCutGap.PhysicalIntegerRoundingCost

open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal
open OriginalGraphCostEnvelope (preparedCells preparedCells_eq packedCost)
open RawGraphControllerProgram (instructionBound chargeBound)
open RetainedGridState (PairFlags)
open PhysicalIntegerRounding (Result)
open IntegralNetworkFlow
open IntegerEpochParameters (cap)
open Polynomial

private theorem execute_bounded {C H A fuel paid charge : ℕ} {program : Program C} {input out : BitState C}
    (bounded : input.Bounded H A)
    (run : GuardedReferenceExecution.execute program fuel input paid=some (out,charge)) :
    out.Bounded (H+fuel) (A+fuel) := by
  induction fuel generalizing H A input paid with
  | zero => simp [GuardedReferenceExecution.execute] at run
  | succ fuel ih =>
    by_cases deny : GuardedReferenceExecution.needsBit (program input.pc)=true ∧ input.source=[]
    · simp [GuardedReferenceExecution.execute,deny] at run
    · cases step : (attempt program input).result with
      | none =>
        simp only [GuardedReferenceExecution.execute,deny,ite_false,step,Option.some.injEq,Prod.mk.injEq] at run
        rw [← run.1]
        exact bounded.mono (by omega) (by omega)
      | some next =>
        simp only [GuardedReferenceExecution.execute,deny,ite_false,step] at run
        have ok : tick program input=some next := (attempt_result program input).symm.trans step
        have b := ih (tick_controlled bounded ok).1 run
        simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using b

def readBound (n L T : ℕ) : ℕ :=
  let H := preparedCells n L T
  let fuel := instructionBound n L (H+1) T.bits+1
  PhysicalCoverAccess.wordBound (H+1+fuel) (H+fuel)

def roundBudget (n L T : ℕ) : ℕ :=
  EncodedEpochParameters.operationBound n+2*n+10+
    (if L≤n ∧ 64*cap n≤L ∧ n≤L^3 then packedCost n L T+readBound n L T else 0)

set_option maxHeartbeats 1800000 in
theorem hard_paid {n L T : ℕ} {adj : PairFlags n} (positive : 0<L) (tape : Bits) {result : Result n}
    (observed : PhysicalIntegerRounding.hardRun T adj L tape=some result) :
    result.paid≤packedCost n L T+readBound n L T := by
  let F := CandidateEnumeration.make n L
  let E := F.network.enumeration
  let EN := F.nodes.enumeration
  let matrix := GraphRelaxationRefinement.matrix adj
  let H := preparedCells n L T
  let input := RawGraphInputStore.prepare matrix n.bits L.bits T.bits tape
  obtain ⟨data,packing⟩ := RawGraphInputStore.prepare_spec (L:=L) adj T.bits tape
  simp only [preparedCells_eq] at data packing
  have proved := RawGraphControllerProgram.guarded_cut positive EN E input.1
    data.bounded data.entry data.quiet data.dense data.graph data.trials
  rw [value_bits,show input.1.source=tape from rfl] at proved
  cases model : ControllerTapeModel.run positive E (OriginalGraphControllerLaw.ratio n) T
    (OriginalGraphControllerLaw.epochs n) (OriginalGraphControllerLaw.epochs n)
    (PhysicalControllerInitializer.initialCode adj positive) tape with
  | none =>
    rw [model] at proved
    change ∀ limit paid, GuardedReferenceExecution.execute RawGraphControllerProgram.program limit input.1 paid=none at proved
    have stop := proved (instructionBound n L (H+1) T.bits+1) 0
    dsimp only [input,matrix,H] at stop
    simp [PhysicalIntegerRounding.hardRun,preparedCells_eq,stop] at observed
  | some answer =>
    rcases answer with ⟨cut,rest,reads⟩
    rw [model] at proved
    obtain ⟨out,paid,ran,mem,_,_,_,_,time⟩ := proved
    have heap := execute_bounded data.bounded ran
    have addr := Registers.get_all heap.2.2.2.1 .r3
    have store := PhysicalCoverAccess.readWord_charge heap.2.2.1 addr
    have output : (PhysicalCoverAccess.readWord out.heap out.registers.d).1=some cut.data.cut.toList :=
      (PhysicalCoverAccess.readWord_value _ _).trans mem
    have heapSize : out.heap.length≤H+1+(instructionBound n L (H+1) T.bits+1) := by
      have h := heap.1
      change out.heap.length+out.stack.length+1≤H+1+(instructionBound n L (H+1) T.bits+1) at h
      omega
    have lookupCost : (PhysicalCoverAccess.readWord out.heap out.registers.d).2≤readBound n L T := by
      apply store.trans
      change PhysicalCoverAccess.wordBound out.heap.length (H+(instructionBound n L (H+1) T.bits+1)) ≤
        PhysicalCoverAccess.wordBound (H+1+(instructionBound n L (H+1) T.bits+1)) (H+(instructionBound n L (H+1) T.bits+1))
      unfold PhysicalCoverAccess.wordBound PhysicalCoverAccess.cellBound
      gcongr
    have finished : result.paid=input.2+paid+(PhysicalCoverAccess.readWord out.heap out.registers.d).2 := by
      dsimp only [input,matrix] at ran
      simp [PhysicalIntegerRounding.hardRun,preparedCells_eq,ran,output] at observed
      exact congrArg PhysicalIntegerRounding.Result.paid observed.symm
    rw [finished]
    exact Nat.add_le_add (Nat.add_le_add packing time) lookupCost

theorem round_paid {n L T : ℕ} {adj : PairFlags n} (positive : 0<L) (tape : Bits) {result : Result n}
    (observed : PhysicalIntegerRounding.run T adj L tape=some result) :
    result.paid≤roundBudget n L T := by
  have overhead := EncodedEpochParameters.compute_bound n
  by_cases inside : L≤n
  · by_cases hard : 64*cap n≤L ∧ n≤L^3
    · simp only [PhysicalIntegerRounding.run,EncodedEpochParameters.compute_cap,ite_eq_left inside,ite_eq_left hard] at observed
      cases h : PhysicalIntegerRounding.hardRun T adj L tape with
      | none => simp [h] at observed
      | some run =>
        have hbound := hard_paid positive tape h
        simp only [h,Option.map_some,Option.some.injEq] at observed
        rw [← observed,roundBudget,ite_eq_left ⟨inside,hard⟩]
        dsimp only
        omega
    · simp only [PhysicalIntegerRounding.run,EncodedEpochParameters.compute_cap,ite_eq_left inside,
        ite_eq_right hard,Option.some.injEq] at observed
      rw [← observed,roundBudget,ite_eq_right (fun pair => hard pair.2)]
      dsimp only
      omega
  · simp only [PhysicalIntegerRounding.run,ite_eq_right inside,Option.some.injEq] at observed
    rw [← observed,roundBudget,ite_eq_right (fun pair => inside pair.1)]
    dsimp only
    omega

theorem eval_mono (p : Polynomial ℕ) {a b : ℕ} (le : a≤b) : p.eval a≤p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [eval_add] using Nat.add_le_add hp hq
  | monomial k c =>
    rw [eval_monomial,eval_monomial]
    gcongr

private theorem bits_le (k : ℕ) : k.bits.length≤k := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr Nat.lt_two_pow_self

private theorem fuel_le_packed (n L T : ℕ) :
    instructionBound n L (preparedCells n L T+1) T.bits+1≤packedCost n L T := by
  let H := preparedCells n L T
  let t := instructionBound n L (H+1) T.bits
  have step : t+1≤(t+1)*GuardedReferenceExecution.guardCost 26704 := by
    have positive : 1≤GuardedReferenceExecution.guardCost 26704 := by decide
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (t+1) positive
  exact step.trans ((Nat.le_add_left _ _).trans (Nat.le_add_left _ _))

private theorem read_le_eval {n L T : ℕ} (inside : L≤n) {g : ℕ}
    (physical : packedCost n L T≤g) :
    readBound n L T≤128*(16*(n+T+1)^2+g)*(16*(n+T+1)^2+g+1)^2 := by
  let H := preparedCells n L T
  let t := instructionBound n L (H+1) T.bits+1
  let Q := 16*(n+T+1)^2+g
  have init : H+1≤16*(n+T+1)^2 := by
    have nh := bits_le n
    have lh := bits_le L
    have th := bits_le T
    unfold H preparedCells
    nlinarith [Nat.zero_le n,Nat.zero_le T,Nat.zero_le (n*T),sq_nonneg T]
  have time : t≤g := (fuel_le_packed n L T).trans physical
  have heap : H+1+t≤Q := Nat.add_le_add init time
  have width : H+t≤Q := by omega
  change PhysicalCoverAccess.wordBound (H+1+t) (H+t)≤128*Q*(Q+1)^2
  calc
    _ ≤ PhysicalCoverAccess.wordBound Q Q := by
      unfold PhysicalCoverAccess.wordBound PhysicalCoverAccess.cellBound
      gcongr
    _ = _ := by simp only [PhysicalCoverAccess.wordBound,PhysicalCoverAccess.cellBound]; ring

theorem round_budget_polynomial :
    ∃ p : Polynomial ℕ, ∀ n L T, roundBudget n L T≤p.eval (n+T) := by
  obtain ⟨p,h⟩ := OriginalGraphCostEnvelope.bounded_trials_polynomial
  let v := C 16*(X+1)^2+p
  let extra := C 18*X^3+C 14*X+C 75
  refine ⟨p+C 128*v*(v+1)^2+extra,?_⟩
  intro n L T
  let x := n+T
  have head : EncodedEpochParameters.operationBound n+2*n+10≤18*x^3+14*x+75 := by
    have hp : n^3≤x^3 := Nat.pow_le_pow_left (Nat.le_add_right n T) 3
    dsimp only [x] at hp
    unfold EncodedEpochParameters.operationBound x
    omega
  simp only [eval_add,eval_mul,eval_pow,eval_X,eval_C,eval_one,v,extra]
  unfold roundBudget
  split
  next hard =>
    have hp := h n L T hard.1
    have hr := read_le_eval hard.1 hp
    change _ ≤ p.eval x+128*(16*(x+1)^2+p.eval x)*(16*(x+1)^2+p.eval x+1)^2+(18*x^3+14*x+75)
    exact (Nat.add_le_add head (Nat.add_le_add hp hr)).trans_eq (by ac_rfl)
  next =>
    dsimp only [x] at head
    omega

end DirectedFlowCutGap.PhysicalIntegerRoundingCost
