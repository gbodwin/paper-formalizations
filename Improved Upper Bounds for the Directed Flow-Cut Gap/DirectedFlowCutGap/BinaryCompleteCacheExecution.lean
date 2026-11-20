import DirectedFlowCutGap.BinaryGuardedCacheExecution

/-! The terminal-inclusive source dispatcher supplies a proof of a completed
reference execution. The binary driver uses this proof for recursion while
preserving its exact cached state and its unguarded legacy charge. -/
namespace DirectedFlowCutGap.BinaryCompleteCacheExecution

open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal
open CachedReferenceExecution (FastState FastAttempt FastResult)
open CachedScalarRead (sumMeasured sum_value sum_paid)

def Next {C : ℕ} (program : Program C) (next state : FastState C) : Prop :=
  ∃ step, CachedReferenceExecution.attempt program state = .completed step ∧ step.state = next

abbrev Ready {C : ℕ} (program : Program C) := {state : FastState C // Acc (Next program) state}

private theorem lift_access {C : ℕ} {program : Program C} {state : FastState C}
    (accessible : Acc (Next program) state) :
    ∀ proof : Acc (Next program) state,
      Acc (fun u v : Ready program => Next program u.1 v.1) ⟨state, proof⟩ := by
  induction accessible with
  | intro state _ ih =>
      intro witness
      exact .intro _ (fun next progress => ih next.1 progress next.2)

instance {C : ℕ} (program : Program C) : WellFoundedRelation (Ready program) :=
  ⟨fun u v => Next program u.1 v.1, ⟨fun s => lift_access s.2 s.2⟩⟩

theorem ready_of_success {C fuel paid : ℕ} {program : Program C} {state : FastState C}
    {answer : FastState C × ℕ} (done : CachedReferenceExecution.execute program fuel state paid = some answer) :
    Acc (Next program) state := by
  induction fuel generalizing state paid with
  | zero => cases done
  | succ fuel ih =>
      refine .intro state ?_
      rintro _ ⟨step, ran, rfl⟩
      rw [CachedReferenceExecution.execute, ran] at done
      exact ih done

private def executeFrom {C : ℕ} (program : Program C) (ready : Ready program) (paid extra : ℕ) :
    (FastState C × ℕ) × ℕ :=
  let measured := CachedBinaryAttempt.attempt program ready.1
  match ran : measured.1 with
  | .stopped state fee =>
    let bill := sumMeasured [paid, fee]
    ((state, bill.1), extra + measured.2 + bill.2)
  | .completed step =>
    let old : CachedReferenceExecution.attempt program ready.1 = .completed step :=
      (CachedBinaryAttempt.value_eq program ready.1).symm.trans ran
    let advance : Next program step.state ready.1 := ⟨step, old, rfl⟩
    let bill := sumMeasured [paid, step.cost]
    executeFrom program ⟨step.state, ready.2.inv advance⟩ bill.1 (extra + measured.2 + bill.2)
termination_by ready
decreasing_by exact advance

def execute {C : ℕ} (program : Program C) (state : Ready program) (paid : ℕ) : (FastState C × ℕ) × ℕ :=
  executeFrom program state paid 0

private theorem observesFrom {C fuel paid extra : ℕ} {program : Program C} {state : Ready program}
    {answer : FastState C × ℕ}
    (done : CachedReferenceExecution.execute program fuel state.1 paid = some answer) :
    (executeFrom program state paid extra).1 = answer := by
  induction fuel generalizing state paid extra with
  | zero => cases done
  | succ fuel ih =>
      rw [executeFrom]
      dsimp only
      split
      · rename_i out fee ran
        have seen := (CachedBinaryAttempt.value_eq program state.1).symm.trans ran
        rw [CachedReferenceExecution.execute, seen] at done
        simpa only [sum_value,List.sum_cons,List.sum_nil,Nat.add_zero] using Option.some.inj done
      · rename_i next ran
        have seen := (CachedBinaryAttempt.value_eq program state.1).symm.trans ran
        rw [CachedReferenceExecution.execute, seen] at done
        simp only [sum_value,List.sum_cons,List.sum_nil,Nat.add_zero]
        exact ih done

theorem observes {C fuel paid : ℕ} {program : Program C} {state : Ready program} {answer : FastState C × ℕ}
    (done : CachedReferenceExecution.execute program fuel state.1 paid = some answer) :
    (execute program state paid).1 = answer := observesFrom done

theorem reached {C fuel paid H B : ℕ} {program : Program C} {state : FastState C}
    {answer : FastState C × ℕ} (done : CachedReferenceExecution.execute program fuel state paid = some answer)
    (fits : state.freeze.Bounded H B) : answer.1.freeze.Bounded (H+fuel) (B+fuel) := by
  induction fuel generalizing state paid H B with
  | zero => cases done
  | succ fuel ih =>
      cases ran : CachedReferenceExecution.attempt program state with
      | stopped final cost =>
          rw [CachedReferenceExecution.execute,ran] at done
          have original := CachedReferenceExecution.stopped_state program ran
          have answerState : final = answer.1 := congrArg Prod.fst (Option.some.inj done)
          rw [← answerState,original]
          exact fits.mono (by omega) (by omega)
      | completed step =>
          rw [CachedReferenceExecution.execute,ran] at done
          have ticked : tick program state.freeze = some step.freeze := by
            rw [← ImmutableReferenceTerminal.attempt_result,← CachedReferenceExecution.attempt_eq,ran]
            rfl
          have returned := ih done (tick_controlled fits ticked).1
          exact returned.mono (by omega) (by omega)

private theorem bill_bound {paid cost limit : ℕ} (cap : paid+cost ≤ limit) :
    (sumMeasured [paid, cost]).2 ≤ BinaryGuardedCacheExecution.additionBudget limit := by
  have sized : ([paid, cost] : List ℕ).sum.size ≤ limit.size := by
    simpa only [List.sum_cons,List.sum_nil,Nat.add_zero] using Nat.size_le_size cap
  exact (sum_paid _ sized).trans (by
    simp only [BinaryGuardedCacheExecution.additionBudget,List.length_cons,List.length_nil]
    omega)

attribute [local irreducible] CachedBinaryAttempt.attempt CachedBinaryAttempt.budget CachedScalarRead.sumMeasured

set_option maxHeartbeats 1200000 in
private theorem paidFrom {C fuel paid extra H B maxH maxB limit : ℕ} {program : Program C}
    {state : Ready program} {answer : FastState C × ℕ}
    (done : CachedReferenceExecution.execute program fuel state.1 paid = some answer)
    (fits : state.1.freeze.Bounded H B) (cells : H+fuel ≤ maxH) (width : B+fuel ≤ maxB)
    (room : paid+fuel*stepBound C maxH maxB ≤ limit) :
    (executeFrom program state paid extra).2 ≤ extra+fuel*(CachedBinaryAttempt.budget C maxH maxB+
      BinaryGuardedCacheExecution.additionBudget limit) := by
  induction fuel generalizing state paid extra H B with
  | zero => cases done
  | succ fuel ih =>
      let upper := stepBound C maxH maxB
      let cycle := CachedBinaryAttempt.budget C maxH maxB+BinaryGuardedCacheExecution.additionBudget limit
      have wide : state.1.freeze.Bounded maxH maxB := fits.mono (by omega) (by omega)
      have measured := CachedBinaryAttempt.paid program state.1 wide
      have old := ImmutableReferenceTerminal.attempt_bound (p:=program) wide
      rw [← CachedReferenceExecution.attempt_eq, ← CachedBinaryAttempt.value_eq] at old
      have available : paid+(fuel+1)*upper≤limit := room
      rw [Nat.add_mul,Nat.one_mul] at available
      rw [executeFrom]
      dsimp only
      split
      · rename_i final cost ran
        rw [ran] at old
        change cost≤upper at old
        have fee := bill_bound (paid:=paid) (cost:=cost) (limit:=limit) (by omega)
        change extra+(CachedBinaryAttempt.attempt program state.1).2+(sumMeasured [paid,cost]).2≤extra+(fuel+1)*cycle
        rw [Nat.add_mul,Nat.one_mul]
        have first : (CachedBinaryAttempt.attempt program state.1).2+(sumMeasured [paid,cost]).2≤cycle :=
          Nat.add_le_add measured fee
        omega
      · rename_i next ran
        have seen := (CachedBinaryAttempt.value_eq program state.1).symm.trans ran
        rw [CachedReferenceExecution.execute, seen] at done
        rw [ran] at old
        change next.cost≤upper at old
        have ticked : tick program state.1.freeze=some next.freeze := by
          rw [← ImmutableReferenceTerminal.attempt_result, ← CachedReferenceExecution.attempt_eq, seen]
          rfl
        let total := sumMeasured [paid,next.cost]
        have sum_eq : total.1=paid+next.cost := by
          simp only [total,sum_value,List.sum_cons,List.sum_nil,Nat.add_zero]
        have first := bill_bound (paid:=paid) (cost:=next.cost) (limit:=limit) (by omega)
        have still : total.1+fuel*upper≤limit := by omega
        have continued : CachedReferenceExecution.execute program fuel next.state total.1=some answer := by
          rw [sum_eq]
          exact done
        let extra' := extra+(CachedBinaryAttempt.attempt program state.1).2+total.2
        have nextCharge : extra'≤extra+cycle := by
          have iterationCost : (CachedBinaryAttempt.attempt program state.1).2+total.2≤cycle :=
            Nat.add_le_add measured first
          omega
        let advance : Next program next.state state.1 := ⟨next, seen, rfl⟩
        have tail := ih (state:=⟨next.state,state.2.inv advance⟩) (extra:=extra') continued
          (tick_controlled fits ticked).1 (by omega) (by omega) still
        change (executeFrom program ⟨next.state,state.2.inv advance⟩ total.1 extra').2≤extra+(fuel+1)*cycle
        rw [Nat.add_mul,Nat.one_mul]
        change _≤extra'+fuel*cycle at tail
        exact tail.trans (by omega)

theorem paid {C fuel paid H B maxH maxB limit : ℕ} {program : Program C}
    {state : Ready program} {answer : FastState C × ℕ}
    (done : CachedReferenceExecution.execute program fuel state.1 paid = some answer)
    (fits : state.1.freeze.Bounded H B) (cells : H+fuel≤maxH) (width : B+fuel≤maxB)
    (room : paid+fuel*stepBound C maxH maxB≤limit) :
    (execute program state paid).2≤fuel*(CachedBinaryAttempt.budget C maxH maxB+BinaryGuardedCacheExecution.additionBudget limit) := by
  simpa only [execute,Nat.zero_add] using
    paidFrom (extra:=0) done fits cells width room

end DirectedFlowCutGap.BinaryCompleteCacheExecution
