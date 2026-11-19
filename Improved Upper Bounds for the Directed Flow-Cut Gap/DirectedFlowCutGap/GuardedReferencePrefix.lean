import DirectedFlowCutGap.GuardedReferenceExecution

/-! A successful unguarded prefix that asks for too many bits forces guarded rejection. -/

namespace DirectedFlowCutGap.GuardedReferencePrefix

open ImmutableReferenceSimulation ImmutableReferenceTerminal GuardedReferenceExecution

theorem rejects_prefix {C t q : ℕ} {p : Program C} {s u : BitState C} {events : List Event}
    (run : Run p t q s events u) (missing : s.source.length<requestCount events)
    (fuel paid : ℕ) : execute p fuel s paid=none := by
  induction run generalizing fuel paid with
  | done => simp [requestCount] at missing
  | @step initial finish next steps cost es tick body ih =>
    cases fuel with
    | zero => rfl
    | succ fuel =>
      by_cases guard : needsBit (p initial.pc)=true ∧ initial.source=[]
      · simp [execute,guard]
      · have succeeds : (attempt p initial).result=some next := (attempt_result p initial).trans tick
        have enough : requestCount next.events≤ initial.source.length := by
          rw [(tick_requests tick).1]
          cases h : needsBit (p initial.pc) <;> cases t : initial.source <;> simp_all
        have short : next.state.source.length<requestCount es := by
          rw [(tick_requests tick).2,List.length_drop]
          rw [count_append] at missing
          omega
        simp only [execute,guard,ite_false,succeeds]
        exact ih short fuel _

end DirectedFlowCutGap.GuardedReferencePrefix
