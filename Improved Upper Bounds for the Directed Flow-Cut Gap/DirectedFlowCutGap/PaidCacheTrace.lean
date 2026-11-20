import DirectedFlowCutGap.CachedControllerStorage
import DirectedFlowCutGap.PaidTotalGuardedExecution

/-! Count conservative persistent-array copies over the exact cached steps
executed before halt or the first unavailable tape bit. -/
namespace DirectedFlowCutGap.PaidCacheTrace

open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal
open CachedReferenceExecution (FastState FastResult FastAttempt)
open TotalGuardedPackedExecution (Next Ready blocked)
open GuardedReferenceExecution (needsBit guardCost)

def allocation {C : ℕ} (p : Program C) (s : FastState C) : Option (Cell Bits) :=
  match p s.pc with
  | .make _ recipe _ => some (recipe.cell s.registers)
  | .request _ _ => some (.flag (s.source.headD false))
  | _ => none

/-- The components are allocated cells and copying instructions. The constants
come from the three exact array traces in `CachedHeapCopies.append_copies`. -/
def traffic {C : ℕ} (p : Program C) (s : FastState C) : ℕ × ℕ :=
  match allocation p s with
  | none => (0,0)
  | some _ => (3*s.store.cells.size+11,12*s.store.cells.size+23)

theorem allocated_store {C : ℕ} {p : Program C} {s next : FastState C} {c : Cell Bits}
    (moved : Next p next s) (selected : allocation p s=some c) :
    next.store=(CachedReferenceHeap.append s.store c).1 := by
  obtain ⟨_,result,completed,rfl⟩ := moved
  cases label : p s.pc <;> simp only [allocation,label,reduceCtorEq,Option.some.injEq] at selected
  all_goals
    subst c
    rw [CachedReferenceExecution.attempt,label] at completed
    rw [← FastAttempt.completed.inj completed]
    cases s
    rfl

theorem traffic_fits {C H B : ℕ} (p : Program C) (s : FastState C) (bounded : s.freeze.Bounded H B) :
    (traffic p s).1 ≤ 3*H+11 ∧ (traffic p s).2 ≤ 12*H+23 := by
  have records := bounded.1
  simp only [State.records,FastState.freeze,Array.length_toList] at records
  unfold traffic
  cases allocation p s <;> (constructor <;> dsimp only <;> omega)

inductive Walk {C : ℕ} (p : Program C) : FastState C → ℕ → ℕ → ℕ → FastState C → Prop where
  | done (s : FastState C) : Walk p s 0 0 0 s
  | step {s next final : FastState C} {steps cells copies : ℕ} :
      Next p next s → Walk p next steps cells copies final →
      Walk p s (steps+1) ((traffic p s).1+cells) ((traffic p s).2+copies) final

private theorem attempt_result {C : ℕ} (p : Program C) (s : FastState C) :
    (CachedReferenceExecution.attempt p s).freeze.result=tick p s.freeze :=
  (congrArg Attempt.result (CachedReferenceExecution.attempt_eq p s)).trans
    (ImmutableReferenceTerminal.attempt_result p s.freeze)

theorem Walk.bounded {C H B k a b : ℕ} {p : Program C} {s out : FastState C}
    (walk : Walk p s k a b out) (fits : s.freeze.Bounded H B) :
    out.freeze.Bounded (H+k) (B+k) ∧ a≤k*(3*(H+k)+11) ∧ b≤k*(12*(H+k)+23) := by
  induction walk generalizing H B with
  | done s => simpa only [Nat.add_zero,Nat.zero_mul,le_refl,and_true] using fits
  | @step s next out k cells copies moved rest ih =>
      obtain ⟨_,r,completed,rfl⟩ := moved
      have result := attempt_result p s
      rw [completed] at result
      have step : tick p s.freeze=some r.freeze := result.symm
      have nextFits : r.state.freeze.Bounded (H+1) (B+1) := (tick_controlled fits step).1
      obtain ⟨finalFit,allocations,instructions⟩ := ih nextFits
      obtain ⟨firstCells,firstCopies⟩ := traffic_fits p s fits
      have h : H+1+k=H+(k+1) := by omega
      have w : B+1+k=B+(k+1) := by omega
      rw [h,w] at finalFit
      rw [h] at allocations instructions
      refine ⟨finalFit,?_,?_⟩
      · rw [Nat.add_mul,Nat.one_mul]
        omega
      · rw [Nat.add_mul,Nat.one_mul]
        omega

private theorem stopped_value {C : ℕ} {p : Program C} (s : Ready p) (paid : ℕ)
    (guard : ¬blocked p s.1) {u : FastState C} {cost : ℕ}
    (ran : CachedReferenceExecution.attempt p s.1=.stopped u cost) :
    (PaidTotalGuardedExecution.execute p s paid).1=some u := by
  rw [PaidTotalGuardedExecution.execute,dite_eq_right guard]
  split
  all_goals
    rename_i observed
    rw [ran] at observed
    cases observed <;> rfl

private theorem completed_value {C : ℕ} {p : Program C} (s : Ready p) (paid : ℕ)
    (guard : ¬blocked p s.1) {u : FastResult C}
    (ran : CachedReferenceExecution.attempt p s.1=.completed u) :
    let moved : Next p u.state s.1 := ⟨guard,u,ran,rfl⟩
    (PaidTotalGuardedExecution.execute p s paid).1=
      (PaidTotalGuardedExecution.execute p ⟨u.state,s.2.inv moved⟩ (paid+u.cost+guardCost C)).1 := by
  dsimp only
  rw [PaidTotalGuardedExecution.execute,dite_eq_right guard]
  split
  all_goals
    rename_i observed
    rw [ran] at observed
    cases observed <;> rfl

/-- Reached states and counted copies follow the actual fuel-free runner.
A complete raw reference trace gives a bound on the walked prefix length. -/
theorem run_walk {C t q : ℕ} {p : Program C} {initial out : BitState C} {events : List Event}
    (trace : Run p t q initial events out) (halt : p out.pc=.halt)
    (s : Ready p) (init : s.1.freeze=initial) (paid : ℕ) :
    ∃ k≤t, ∃ cells copies stop, Walk p s.1 k cells copies stop ∧
      match (PaidTotalGuardedExecution.execute p s paid).1 with
      | none => blocked p stop
      | some final => final=stop ∧ p stop.pc=.halt := by
  induction trace generalizing s paid with
  | done state =>
      have pc : p s.1.pc=.halt := by
        change p s.1.freeze.pc=.halt
        rw [init,halt]
      have notBlocked : ¬blocked p s.1 := by simp [blocked,pc,needsBit]
      have observed := attempt_result p s.1
      have tickHalt : tick p s.1.freeze=none := by
        have label : p s.1.freeze.pc=.halt := pc
        rw [tick,label]
      rw [tickHalt] at observed
      cases ran : CachedReferenceExecution.attempt p s.1 with
      | stopped final cost =>
        have same := CachedReferenceExecution.stopped_state p ran
        rw [stopped_value s paid notBlocked ran]
        exact ⟨0,le_rfl,0,0,s.1,.done _,same,pc⟩
      | completed body =>
        rw [ran] at observed
        cases observed
  | @step initial next reference t q events first rest ih =>
      by_cases guard : blocked p s.1
      · rw [PaidTotalGuardedExecution.execute,dite_eq_left guard]
        exact ⟨0,Nat.zero_le _,0,0,s.1,.done _,guard⟩
      · have observed := attempt_result p s.1
        rw [init,first] at observed
        cases ran : CachedReferenceExecution.attempt p s.1 with
        | stopped final cost =>
          rw [ran] at observed
          cases observed
        | completed step =>
          have moved : Next p step.state s.1 := ⟨guard,step,ran,rfl⟩
          rw [ran] at observed
          have same : step.state.freeze=reference.state :=
            congrArg (fun r : Result Bits C => r.state) (Option.some.inj observed)
          obtain ⟨k,within,cells,copies,stop,run,done⟩ := ih halt ⟨step.state,s.2.inv moved⟩ same
            (paid+step.cost+guardCost C)
          rw [completed_value s paid guard ran]
          exact ⟨k+1,Nat.succ_le_succ within,_,_,stop,.step moved run,done⟩

end DirectedFlowCutGap.PaidCacheTrace
