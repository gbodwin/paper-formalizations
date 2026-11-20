import DirectedFlowCutGap.PaidCacheTrace

/-! A completed trace that fits its literal source yields the same cache
walk for the guarded and the terminal-inclusive evaluators. -/
namespace DirectedFlowCutGap.CompleteCacheTraffic

open ImmutableReferenceSimulation ImmutableReferenceTerminal
open CachedReferenceExecution (FastState FastAttempt FastResult)
open GuardedReferenceExecution (requestCount count_append tick_requests)
open TotalGuardedPackedExecution (blocked Next)
open PaidCacheTrace (Walk)

private theorem observed {C : ℕ} (program : Program C) (state : FastState C) :
    (CachedReferenceExecution.attempt program state).freeze.result=tick program state.freeze := by
  rw [CachedReferenceExecution.attempt_eq,ImmutableReferenceTerminal.attempt_result]

theorem complete_walk {C steps cost : ℕ} {program : Program C} {start out : BitState C}
    {events : List Event} (ran : Run program steps cost start events out)
    (enough : requestCount events ≤ start.source.length) (state : FastState C) (init : state.freeze=start) :
    ∃ cells copies done, Walk program state steps cells copies done ∧ done.freeze=out := by
  induction ran generalizing state with
  | done => exact ⟨0,0,state,.done state,init⟩
  | @step start out first steps cost events ran rest ih =>
      rw [count_append] at enough
      obtain ⟨requested, suffix⟩ := tick_requests ran
      have remaining : requestCount events ≤ first.state.source.length := by
        rw [suffix,List.length_drop]
        omega
      have free : ¬ blocked program state := by
        rintro ⟨atRequest,empty⟩
        have label : state.pc=start.pc := congrArg (fun s : BitState C => s.pc) init
        have tape : state.source=start.source := congrArg (fun s : BitState C => s.source) init
        rw [← label,atRequest] at requested
        rw [← tape,empty,List.length_nil] at enough
        simp only [Bool.toNat_true] at requested
        omega
      have outcome := observed program state
      rw [init,ran] at outcome
      cases attempt : CachedReferenceExecution.attempt program state with
      | stopped _ _ =>
          rw [attempt] at outcome
          cases outcome
      | completed step =>
          rw [attempt] at outcome
          have same : step.state.freeze=first.state :=
            congrArg (fun r : Result BinaryArithmetic.Bits C => r.state) (Option.some.inj outcome)
          obtain ⟨cells,copies,done,tail,agrees⟩ := ih remaining step.state same
          have progress : Next program step.state state := ⟨free,step,attempt,rfl⟩
          exact ⟨_,_,done,.step progress tail,agrees⟩

/-- A walk through a terminal state identifies the actual cached result,
including the store with its two retained prefix arrays. -/
theorem execute_walk {C steps cells copies : ℕ} {program : Program C} {start out : FastState C}
    (walk : Walk program start steps cells copies out) (stop : tick program out.freeze=none)
    (fuel paid : ℕ) (within : steps<fuel) :
    ∃ charge, CachedReferenceExecution.execute program fuel start paid = some (out,charge) := by
  induction walk generalizing fuel paid with
  | done state =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have actual := (observed program state).trans stop
          cases attempt : CachedReferenceExecution.attempt program state with
          | stopped last cost =>
              have eq := CachedReferenceExecution.stopped_state program attempt
              exact ⟨paid+cost,by rw [CachedReferenceExecution.execute,attempt,eq]⟩
          | completed step =>
              rw [attempt] at actual
              cases actual
  | @step state successor out steps cells copies next walk ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          obtain ⟨_, body, seen, rfl⟩ := next
          obtain ⟨q, observed⟩ := ih stop fuel (paid+body.cost) (by omega)
          exact ⟨q,by rw [CachedReferenceExecution.execute,seen]; exact observed⟩

end DirectedFlowCutGap.CompleteCacheTraffic
