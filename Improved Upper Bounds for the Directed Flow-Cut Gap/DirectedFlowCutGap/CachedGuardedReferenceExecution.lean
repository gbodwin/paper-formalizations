import DirectedFlowCutGap.CachedReferenceExecution
import DirectedFlowCutGap.GuardedReferenceExecution

/-! The cached store preserves the guarded machine's tape, terminal state,
and reference operation count, including the cost of every guard. -/
namespace DirectedFlowCutGap.CachedGuardedReferenceExecution

open ImmutableReferenceSimulation ImmutableReferenceTerminal CachedReferenceExecution
open GuardedReferenceExecution (needsBit guardCost)

def execute {C : ℕ} (p : Program C) : ℕ → FastState C → ℕ → Option (FastState C × ℕ)
  | 0, _, _ => none
  | fuel+1, s, paid =>
    if needsBit (p s.pc) = true ∧ s.source = [] then none
    else
      match CachedReferenceExecution.attempt p s with
      | .stopped u q => some (u,paid+q+guardCost C)
      | .completed r => execute p fuel r.state (paid+r.cost+guardCost C)

theorem execute_eq {C : ℕ} (p : Program C) (fuel : ℕ) (s : FastState C) (paid : ℕ) :
    (execute p fuel s paid).map (fun (u,q) => (u.freeze,q)) =
      GuardedReferenceExecution.execute p fuel s.freeze paid := by
  induction fuel generalizing s paid with
  | zero => rfl
  | succ fuel ih =>
    by_cases guarded : needsBit (p s.pc) = true ∧ s.source = []
    · have frozen : needsBit (p s.freeze.pc) = true ∧ s.freeze.source = [] := guarded
      rw [execute,GuardedReferenceExecution.execute,ite_eq_left guarded,ite_eq_left frozen]
      rfl
    · have frozen : ¬ (needsBit (p s.freeze.pc) = true ∧ s.freeze.source = []) := guarded
      rw [execute,GuardedReferenceExecution.execute,ite_eq_right guarded,ite_eq_right frozen]
      have same := CachedReferenceExecution.attempt_eq p s
      cases h : CachedReferenceExecution.attempt p s with
      | stopped u q =>
        have equal := CachedReferenceExecution.stopped_state p h
        subst u
        rw [h] at same
        simp only [Option.map_some,← same,FastAttempt.freeze,stopped]
      | completed r =>
        rw [h] at same
        simp only [← same,FastAttempt.freeze,success,FastResult.freeze]
        exact ih r.state (paid+r.cost+guardCost C)

theorem execute_ofReference {C : ℕ} (p : Program C) (fuel : ℕ) (s : BitState C) (paid : ℕ) :
    (execute p fuel (FastState.ofReference s) paid).map (fun (u,q) => (u.freeze,q)) =
      GuardedReferenceExecution.execute p fuel s paid := by
  simpa only [freeze_ofReference] using execute_eq p fuel (FastState.ofReference s) paid

end DirectedFlowCutGap.CachedGuardedReferenceExecution
