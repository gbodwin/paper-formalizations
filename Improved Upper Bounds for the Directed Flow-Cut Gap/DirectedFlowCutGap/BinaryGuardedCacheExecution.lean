import DirectedFlowCutGap.CachedBinaryAttempt
import DirectedFlowCutGap.PaidTotalGuardedExecution

/-! Feed the binary cached operations into the same guarded recursion. The
extra count records their arithmetic and the running-charge additions. Both
work totals are carried forward in tail position. -/
namespace DirectedFlowCutGap.BinaryGuardedCacheExecution

open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal
open CachedReferenceExecution (FastState FastAttempt FastResult)
open TotalGuardedPackedExecution (Next Ready blocked)
open GuardedReferenceExecution (guardCost)
open CachedScalarRead (sumMeasured sum_value sum_paid)

private def executeFrom {C : ℕ} (p : Program C) (s : Ready p) (paid extra : ℕ) :
    (Option (FastState C) × ℕ) × ℕ :=
  if guard : blocked p s.1 then
    let fee := sumMeasured [paid,guardCost C]
    ((none,fee.1),extra+fee.2)
  else
    let measured := CachedBinaryAttempt.attempt p s.1
    match result : measured.1 with
    | .stopped final cost =>
        let fee := sumMeasured [paid,cost,guardCost C]
        ((some final,fee.1),extra+measured.2+fee.2)
    | .completed step =>
        let seen : CachedReferenceExecution.attempt p s.1=.completed step :=
          (CachedBinaryAttempt.value_eq p s.1).symm.trans result
        let progressed : Next p step.state s.1 := ⟨guard,step,seen,rfl⟩
        let fee := sumMeasured [paid,step.cost,guardCost C]
        executeFrom p ⟨step.state,s.2.inv progressed⟩ fee.1 (extra+measured.2+fee.2)
termination_by s
decreasing_by exact progressed

def execute {C : ℕ} (p : Program C) (s : Ready p) (paid : ℕ) :
    (Option (FastState C) × ℕ) × ℕ :=
  executeFrom p s paid 0

private theorem old_stop {C : ℕ} (p : Program C) (s : Ready p) (paid : ℕ)
    (guard : ¬blocked p s.1) {final : FastState C} {work : ℕ}
    (what : CachedReferenceExecution.attempt p s.1=.stopped final work) :
    PaidTotalGuardedExecution.execute p s paid=(some final,paid+work+guardCost C) := by
  rw [PaidTotalGuardedExecution.execute,dite_eq_right guard]
  split
  all_goals
    rename_i ran
    rw [what] at ran
    cases ran <;> rfl

private theorem old_next {C : ℕ} (p : Program C) (s : Ready p) (paid : ℕ)
    (guard : ¬blocked p s.1) {r : FastResult C}
    (what : CachedReferenceExecution.attempt p s.1=.completed r) :
    let moved : Next p r.state s.1 := ⟨guard,r,what,rfl⟩
    PaidTotalGuardedExecution.execute p s paid=
      PaidTotalGuardedExecution.execute p ⟨r.state,s.2.inv moved⟩ (paid+r.cost+guardCost C) := by
  dsimp only
  rw [PaidTotalGuardedExecution.execute,dite_eq_right guard]
  split
  all_goals
    rename_i ran
    rw [what] at ran
    cases ran <;> rfl

set_option maxHeartbeats 800000 in
private theorem observesFrom {C : ℕ} (p : Program C) (s : Ready p) (paid extra : ℕ) :
    (executeFrom p s paid extra).1=PaidTotalGuardedExecution.execute p s paid := by
  obtain ⟨start,accessible⟩ := s
  induction accessible generalizing paid extra with
  | intro state reach ih =>
    let ready : Ready p := ⟨state,.intro state reach⟩
    change (executeFrom p ready paid extra).1=PaidTotalGuardedExecution.execute p ready paid
    rw [executeFrom]
    by_cases blockedHere : blocked p state
    · have found : blocked p ready.1 := blockedHere
      rw [dite_eq_left found,PaidTotalGuardedExecution.execute,dite_eq_left found]
      simp only [sum_value,List.sum_cons,List.sum_nil,Nat.add_zero]
    · have free : ¬blocked p ready.1 := blockedHere
      rw [dite_eq_right free]
      dsimp only
      split
      · rename_i final work observed
        have prior : CachedReferenceExecution.attempt p ready.1=.stopped final work :=
          (CachedBinaryAttempt.value_eq p ready.1).symm.trans observed
        rw [old_stop p ready paid free prior]
        simp only [sum_value,List.sum_cons,List.sum_nil,Nat.add_zero,Nat.add_assoc]
      · rename_i body observed
        have prior : CachedReferenceExecution.attempt p ready.1=.completed body :=
          (CachedBinaryAttempt.value_eq p ready.1).symm.trans observed
        have motion : Next p body.state state := ⟨free,body,prior,rfl⟩
        rw [old_next p ready paid free prior]
        simp only [sum_value,List.sum_cons,List.sum_nil,Nat.add_zero,Nat.add_assoc]
        exact ih body.state motion (paid+(body.cost+guardCost C)) _

theorem observes {C : ℕ} (p : Program C) (s : Ready p) (paid : ℕ) :
    (execute p s paid).1=PaidTotalGuardedExecution.execute p s paid :=
  observesFrom p s paid 0

attribute [local irreducible] CachedBinaryAttempt.attempt CachedBinaryAttempt.budget CachedScalarRead.sumMeasured

def additionBudget (limit : ℕ) : ℕ := 3*(96*(limit.size+2)^2+4)+1

private theorem addition_paid {parts : List ℕ} {limit : ℕ} (length : parts.length≤3)
    (cap : (sumMeasured parts).1≤limit) : (sumMeasured parts).2≤additionBudget limit := by
  rw [sum_value] at cap
  have cost := sum_paid parts (Nat.size_le_size cap)
  exact cost.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ length) 1)

private theorem observed_tick {C : ℕ} (p : Program C) (s : FastState C) :
    (CachedBinaryAttempt.attempt p s).1.freeze.result=tick p s.freeze := by
  rw [CachedBinaryAttempt.value_eq,CachedReferenceExecution.attempt_eq,ImmutableReferenceTerminal.attempt_result]

private theorem observed_bound {C H B : ℕ} (p : Program C) (s : FastState C)
    (fits : s.freeze.Bounded H B) : (CachedBinaryAttempt.attempt p s).1.freeze.operations≤stepBound C H B := by
  rw [CachedBinaryAttempt.value_eq,CachedReferenceExecution.attempt_eq]
  exact ImmutableReferenceTerminal.attempt_bound fits

set_option maxHeartbeats 1200000 in
/-- A supplied complete raw trace bounds all scalar work on the actually
executed prefix. The numerical length and common widths occur in the proof. -/
private theorem paidFrom {C H B t q maxH maxB limit : ℕ} {p : Program C} {initial final : BitState C}
    {events : List Event} (trace : Run p t q initial events final) (halt : tick p final=none)
    (s : Ready p) (init : s.1.freeze=initial) (paid extra : ℕ) (fits : initial.Bounded H B)
    (wideH : H+t≤maxH) (wideB : B+t≤maxB)
    (room : paid+(t+1)*(stepBound C maxH maxB+guardCost C)≤limit) :
    (executeFrom p s paid extra).2≤extra+(t+1)*(CachedBinaryAttempt.budget C maxH maxB+additionBudget limit) := by
  induction trace generalizing s paid extra H B with
  | done atStop =>
      have wide : s.1.freeze.Bounded maxH maxB := by
        rw [init]
        exact fits.mono (by omega) (by omega)
      have count := observed_bound p s.1 wide
      have attempts := CachedBinaryAttempt.paid p s.1 wide
      have base : paid+stepBound C maxH maxB+guardCost C≤limit := by
        simp only [Nat.zero_add,Nat.one_mul] at room
        omega
      rw [executeFrom]
      by_cases unavailable : blocked p s.1
      · rw [dite_eq_left unavailable]
        let fees := [paid,guardCost C]
        have cap : (sumMeasured fees).1≤limit := by
          simp only [fees,sum_value,List.sum_cons,List.sum_nil,Nat.add_zero]
          omega
        have work := addition_paid (parts:=fees) (by simp [fees]) cap
        simp only [Nat.zero_add,Nat.one_mul]
        exact Nat.add_le_add_left (work.trans (Nat.le_add_left _ _)) _
      · rw [dite_eq_right unavailable]
        dsimp only
        have terminal := observed_tick p s.1
        rw [init,halt] at terminal
        split
        · rename_i stopped work seen
          rw [seen] at count
          change work≤stepBound C maxH maxB at count
          let fees := [paid,work,guardCost C]
          have cap : (sumMeasured fees).1≤limit := by
            simp only [fees,sum_value,List.sum_cons,List.sum_nil,Nat.add_zero]
            omega
          have bill := addition_paid (parts:=fees) (by simp [fees]) cap
          simp only [Nat.zero_add,Nat.one_mul]
          exact Nat.add_le_add (Nat.add_le_add_left attempts _) bill |>.trans_eq (Nat.add_assoc ..)
        · rename_i step seen
          rw [seen] at terminal
          cases terminal
  | @step initial final first restCount restWork events ran rest ih =>
      let single := stepBound C maxH maxB+guardCost C
      let cycle := CachedBinaryAttempt.budget C maxH maxB+additionBudget limit
      have wide : s.1.freeze.Bounded maxH maxB := by
        rw [init]
        exact fits.mono (by omega) (by omega)
      have count := observed_bound p s.1 wide
      have attempts := CachedBinaryAttempt.paid p s.1 wide
      have upper : paid+((restCount+1)+1)*single≤limit := room
      have positive : 1≤(restCount+1)+1 := by omega
      have scaled := Nat.mul_le_mul_right single positive
      rw [Nat.one_mul] at scaled
      have base : paid+single≤limit := (Nat.add_le_add_left scaled paid).trans upper
      rw [executeFrom]
      by_cases unavailable : blocked p s.1
      · rw [dite_eq_left unavailable]
        let fees := [paid,guardCost C]
        have cap : (sumMeasured fees).1≤limit := by
          simp only [fees,sum_value,List.sum_cons,List.sum_nil,Nat.add_zero]
          dsimp only [single] at base
          omega
        have bill := addition_paid (parts:=fees) (by simp [fees]) cap
        change extra+(sumMeasured fees).2≤extra+((restCount+1)+1)*cycle
        have part : additionBudget limit≤cycle := Nat.le_add_left _ _
        apply Nat.add_le_add_left
        refine bill.trans (part.trans ?_)
        simpa only [Nat.one_mul] using Nat.mul_le_mul_right cycle positive
      · rw [dite_eq_right unavailable]
        dsimp only
        have advanced := observed_tick p s.1
        rw [init,ran] at advanced
        split
        · rename_i endState charge seen
          rw [seen] at advanced
          cases advanced
        · rename_i next seen
          rw [seen] at advanced count
          have same := Option.some.inj advanced
          have prior : CachedReferenceExecution.attempt p s.1=.completed next :=
            (CachedBinaryAttempt.value_eq p s.1).symm.trans seen
          have progressed : Next p next.state s.1 := ⟨unavailable,next,prior,rfl⟩
          have freezes : next.state.freeze=first.state := congrArg (fun r : Result Bits C => r.state) same
          have nextFits := (tick_controlled fits ran).1
          change next.cost≤stepBound C maxH maxB at count
          let fees := [paid,next.cost,guardCost C]
          have fee : (sumMeasured fees).1≤paid+single := by
            simp only [fees,sum_value,List.sum_cons,List.sum_nil,Nat.add_zero,single]
            omega
          have bill := addition_paid (parts:=fees) (by simp [fees]) (fee.trans base)
          have room' : (sumMeasured fees).1+(restCount+1)*single≤limit := by
            rw [Nat.add_mul,Nat.one_mul] at upper
            omega
          let accumulated := extra+(CachedBinaryAttempt.attempt p s.1).2+(sumMeasured fees).2
          have tail := ih halt ⟨next.state,s.2.inv progressed⟩ freezes (sumMeasured fees).1
            accumulated nextFits (by omega) (by omega) room'
          change (executeFrom p ⟨next.state,s.2.inv progressed⟩ (sumMeasured fees).1 accumulated).2≤
            extra+((restCount+1)+1)*cycle
          have increase : accumulated≤extra+cycle := by
            change extra+(CachedBinaryAttempt.attempt p s.1).2+(sumMeasured fees).2≤extra+cycle
            rw [Nat.add_assoc]
            exact Nat.add_le_add_left (Nat.add_le_add attempts bill) extra
          change _≤accumulated+(restCount+1)*cycle at tail
          rw [Nat.add_mul,Nat.one_mul]
          exact tail.trans (by omega)

theorem paid_of_trace {C H B t q maxH maxB limit : ℕ} {p : Program C} {initial final : BitState C}
    {events : List Event} (trace : Run p t q initial events final) (halt : tick p final=none)
    (s : Ready p) (init : s.1.freeze=initial) (paid : ℕ) (fits : initial.Bounded H B)
    (wideH : H+t≤maxH) (wideB : B+t≤maxB)
    (room : paid+(t+1)*(stepBound C maxH maxB+guardCost C)≤limit) :
    (execute p s paid).2≤(t+1)*(CachedBinaryAttempt.budget C maxH maxB+additionBudget limit) := by
  simpa only [execute,Nat.zero_add] using paidFrom trace halt s init paid 0 fits wideH wideB room

end DirectedFlowCutGap.BinaryGuardedCacheExecution
