import DirectedFlowCutGap.PaidGuardedExecution
import DirectedFlowCutGap.TotalGuardedPackedExecution

/-! Run a proved terminating packed execution without materializing its
analytical fuel. The accessibility certificate is erased by the executable
compiler. Work is retained on both ordinary halt and tape exhaustion. -/
namespace DirectedFlowCutGap.PaidTotalGuardedExecution

open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal
open CachedReferenceExecution (FastState FastAttempt FastResult)
open TotalGuardedPackedExecution (Next Ready blocked)
open GuardedReferenceExecution (needsBit guardCost)

def execute {C : ℕ} (p : Program C) (s : Ready p) (paid : ℕ) : Option (FastState C) × ℕ :=
  if guard : blocked p s.1 then (none,paid+guardCost C)
  else
    match attempt : CachedReferenceExecution.attempt p s.1 with
    | .stopped out work => (some out,paid+work+guardCost C)
    | .completed r =>
        let step : Next p r.state s.1 := ⟨guard,r,attempt,rfl⟩
        execute p ⟨r.state,s.2.inv step⟩ (paid+r.cost+guardCost C)
termination_by s
decreasing_by exact step

private theorem attempt_result {C : ℕ} (p : Program C) (s : FastState C) :
    (CachedReferenceExecution.attempt p s).freeze.result=tick p s.freeze :=
  (congrArg Attempt.result (CachedReferenceExecution.attempt_eq p s)).trans
    (ImmutableReferenceTerminal.attempt_result p s.freeze)

theorem trace_of_success {C fuel paid total : ℕ} {p : Program C} {s out : BitState C}
    (returned : GuardedReferenceExecution.execute p fuel s paid=some (out,total)) :
    ∃ steps<fuel, ∃ work events, Run p steps work s events out ∧ tick p out=none := by
  induction fuel generalizing paid s with
  | zero => cases returned
  | succ fuel ih =>
      rw [GuardedReferenceExecution.execute] at returned
      split at returned
      · cases returned
      · let observed := attempt p s
        let charge := paid+observed.operations+guardCost C
        change (match observed.result with
          | none => some (s,charge)
          | some u => GuardedReferenceExecution.execute p fuel u.state charge)=some (out,total) at returned
        have instruction : observed.result=tick p s := ImmutableReferenceTerminal.attempt_result p s
        cases body : observed.result with
        | none =>
            rw [body] at returned instruction
            have same : s=out := congrArg Prod.fst (Option.some.inj returned)
            subst out
            exact ⟨0,Nat.zero_lt_succ _,0,[],.done _,instruction.symm⟩
        | some result =>
            rw [body] at returned instruction
            obtain ⟨steps,short,work,events,tail,halt⟩ := ih returned
            exact ⟨steps+1,Nat.succ_lt_succ short,_,_,.step instruction.symm tail,halt⟩

/-- A complete reference trace gives a common finite bound for the fuel-free
guarded run and the counted finite driver, including early exhaustion. -/
theorem matches_trace {C t q : ℕ} {p : Program C} {initial out : BitState C} {events : List Event}
    (ran : Run p t q initial events out) (halt : tick p out=none)
    (s : Ready p) (frozen : s.1.freeze=initial) (fuel paid : ℕ) (enough : t<fuel) :
    execute p s paid=PaidGuardedExecution.execute p fuel s.1 paid := by
  induction ran generalizing s fuel paid with
  | done state =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          rw [execute,PaidGuardedExecution.execute]
          by_cases guard : blocked p s.1
          · have empty : needsBit (p s.1.pc)=true ∧ s.1.source=[] := guard
            rw [dite_eq_left guard,ite_eq_left empty]
          · have nonempty : ¬(needsBit (p s.1.pc)=true ∧ s.1.source=[]) := guard
            rw [dite_eq_right guard,ite_eq_right nonempty]
            have value := attempt_result p s.1
            rw [frozen,halt] at value
            split
            · rename_i out work stopped
              rw [stopped]
            · rename_i a completed
              rw [completed] at value
              cases value
  | @step initial next r t q events first rest ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          rw [execute,PaidGuardedExecution.execute]
          by_cases guard : blocked p s.1
          · have empty : needsBit (p s.1.pc)=true ∧ s.1.source=[] := guard
            rw [dite_eq_left guard,ite_eq_left empty]
          · have nonempty : ¬(needsBit (p s.1.pc)=true ∧ s.1.source=[]) := guard
            rw [dite_eq_right guard,ite_eq_right nonempty]
            have value := attempt_result p s.1
            rw [frozen,first] at value
            split
            · rename_i out work stopped
              rw [stopped] at value
              cases value
            · rename_i a performed
              have progress : Next p a.state s.1 := ⟨guard,a,performed,rfl⟩
              rw [performed] at value
              have same : a.state.freeze=r.state :=
                congrArg (fun result : Result Bits C => result.state) (Option.some.inj value)
              conv_rhs => rw [performed]
              exact ih halt ⟨a.state,s.2.inv progress⟩ same fuel (paid+a.cost+guardCost C) (by omega)

end DirectedFlowCutGap.PaidTotalGuardedExecution
