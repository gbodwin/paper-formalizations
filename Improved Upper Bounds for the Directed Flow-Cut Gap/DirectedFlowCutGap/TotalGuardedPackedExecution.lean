import DirectedFlowCutGap.CachedGuardedReferenceExecution

/-! The guarded packed machine can run without computing a fuel bound when
its initial state has a finite trace to halt or tape exhaustion. The
accessibility proof is erased by the executable compiler. -/
namespace DirectedFlowCutGap.TotalGuardedPackedExecution

open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal
open CachedReferenceExecution (FastState FastResult FastAttempt)
open GuardedReferenceExecution (needsBit guardCost tick_requests requestCount count_append)

def blocked {C : ℕ} (p : Program C) (s : FastState C) : Prop :=
  needsBit (p s.pc)=true ∧ s.source=[]

instance {C : ℕ} (p : Program C) (s : FastState C) : Decidable (blocked p s) := by
  unfold blocked
  infer_instance

def Next {C : ℕ} (p : Program C) (u s : FastState C) : Prop :=
  ¬blocked p s ∧ ∃ r, CachedReferenceExecution.attempt p s=.completed r ∧ r.state=u

abbrev Ready {C : ℕ} (p : Program C) := {s : FastState C // Acc (Next p) s}

private theorem lift_access {C : ℕ} (p : Program C) {s : FastState C} (h : Acc (Next p) s) :
    ∀ proof : Acc (Next p) s, Acc (fun u v : Ready p => Next p u.1 v.1) ⟨s,proof⟩ := by
  induction h with
  | intro s _ ih =>
    intro accessible
    exact .intro _ (fun u rel => ih u.1 rel u.2)

instance {C : ℕ} (p : Program C) : WellFoundedRelation (Ready p) :=
  ⟨fun u s => Next p u.1 s.1,⟨fun s => lift_access p s.2 s.2⟩⟩

def execute {C : ℕ} (p : Program C) (s : Ready p) (paid : ℕ) : Option (FastState C × ℕ) :=
  if guard : blocked p s.1 then none
  else
    match h : CachedReferenceExecution.attempt p s.1 with
    | .stopped u q => some (u,paid+q+guardCost C)
    | .completed r =>
      let step : Next p r.state s.1 := ⟨guard,r,h,rfl⟩
      execute p ⟨r.state,s.2.inv step⟩ (paid+r.cost+guardCost C)
termination_by s
decreasing_by
  exact step

private theorem completed_reference {C : ℕ} {p : Program C} {s : FastState C} {r : FastResult C}
    (ran : CachedReferenceExecution.attempt p s=.completed r) :
    (ImmutableReferenceTerminal.attempt p s.freeze).result=some r.freeze := by
  have eq := CachedReferenceExecution.attempt_eq p s
  rw [ran] at eq
  rw [← eq]
  rfl

theorem ready_of_run {C t q : ℕ} {p : Program C} {s u : BitState C} {events : List Event}
    (ran : Run p t q s events u)
    (done : (ImmutableReferenceTerminal.attempt p u).result=none ∨ s.source.length<requestCount events)
    {cache : FastState C} (frozen : cache.freeze=s) : Acc (Next p) cache := by
  induction ran generalizing cache with
  | done state =>
    refine Acc.intro cache ?_
    intro a reached
    obtain ⟨_,r,executed,_⟩ := reached
    have got := completed_reference executed
    rw [frozen] at got
    rcases done with stop | short
    · rw [stop] at got
      cases got
    · simp [requestCount] at short
  | @step initial finish step k cost es tick body ih =>
    refine Acc.intro cache ?_
    intro a reached
    obtain ⟨guard,r,executed,rfl⟩ := reached
    have got := completed_reference executed
    rw [frozen] at got
    have tickResult := (ImmutableReferenceTerminal.attempt_result p initial).trans tick
    have eq := Option.some.inj (got.symm.trans tickResult)
    apply ih _ (congrArg ImmutableReferenceSimulation.Result.state eq)
    rcases done with stop | missing
    · exact Or.inl stop
    · have free : ¬ (needsBit (p initial.pc)=true ∧ initial.source=[]) := by
        simpa only [← frozen,blocked,CachedReferenceExecution.FastState.freeze] using guard
      have enough : requestCount step.events ≤ initial.source.length := by
        rw [(tick_requests tick).1]
        cases h : needsBit (p initial.pc) <;> cases bs : initial.source <;> simp_all
      right
      rw [(tick_requests tick).2,List.length_drop]
      rw [count_append] at missing
      omega

theorem matches_some {C : ℕ} (p : Program C) (fuel : ℕ) (s : Ready p) (paid : ℕ)
    {out : FastState C × ℕ} (ran : CachedGuardedReferenceExecution.execute p fuel s.1 paid=some out) :
    execute p s paid=some out := by
  induction fuel generalizing s paid with
  | zero => cases ran
  | succ fuel ih =>
    rw [execute]
    by_cases guard : blocked p s.1
    · have h : needsBit (p s.1.pc)=true ∧ s.1.source=[] := guard
      simp only [CachedGuardedReferenceExecution.execute,ite_eq_left h] at ran
      cases ran
    · have h : ¬ (needsBit (p s.1.pc)=true ∧ s.1.source=[]) := guard
      rw [dite_eq_right guard]
      simp only [CachedGuardedReferenceExecution.execute,ite_eq_right h] at ran
      split
      · rename_i u work attempt
        simpa only [attempt] using ran
      · rename_i r attempt
        simp only [attempt] at ran
        exact ih _ _ ran

theorem eventual {C : ℕ} (p : Program C) (s : Ready p) (paid : ℕ) :
    ∃ fuel, CachedGuardedReferenceExecution.execute p fuel s.1 paid=execute p s paid := by
  rcases s with ⟨state,accessible⟩
  induction accessible generalizing paid with
  | intro state children ih =>
    by_cases guard : blocked p state
    · have h : needsBit (p state.pc)=true ∧ state.source=[] := guard
      exact ⟨1,by rw [execute,dite_eq_left guard,CachedGuardedReferenceExecution.execute,ite_eq_left h]⟩
    · have h : ¬ (needsBit (p state.pc)=true ∧ state.source=[]) := guard
      rw [execute,dite_eq_right guard]
      split
      · rename_i u work attempt
        exact ⟨1,by simp only [CachedGuardedReferenceExecution.execute,ite_eq_right h,attempt]⟩
      · rename_i r attempt
        have rel : Next p r.state state := ⟨guard,r,attempt,rfl⟩
        obtain ⟨fuel,agrees⟩ := ih r.state rel (paid+r.cost+guardCost C)
        refine ⟨fuel+1,?_⟩
        simp only [CachedGuardedReferenceExecution.execute,ite_eq_right h,attempt]
        exact agrees

end DirectedFlowCutGap.TotalGuardedPackedExecution
