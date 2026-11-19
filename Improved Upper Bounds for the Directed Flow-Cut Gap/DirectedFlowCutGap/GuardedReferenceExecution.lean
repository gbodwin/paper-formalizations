import DirectedFlowCutGap.ImmutableReferenceTerminal

/-!
# Reference execution with an explicit end of tape

The driver checks whether the next instruction needs a bit before making
its ordinary charged attempt. A missing bit reports exhaustion. For
successful runs it preserves the exact old interpreter result and prices
the additional fixed dispatch and source-tag check.
-/

namespace DirectedFlowCutGap.GuardedReferenceExecution

open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal

def needsBit {C : ℕ} : Instruction C → Bool
  | .request .. => true
  | _ => false

def requestCount : List Event → ℕ
  | [] => 0
  | .request _ :: es => requestCount es + 1
  | .emit _ :: es => requestCount es

theorem count_append (a b : List Event) :
    requestCount (a++b) = requestCount a+requestCount b := by
  induction a with
  | nil => simp [requestCount]
  | cons e es ih => cases e <;> simp [requestCount,ih,Nat.add_comm,Nat.add_left_comm]

theorem count_reads (bs : List Bool) : requestCount (bs.map Event.request) = bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [requestCount,ih]

theorem tick_requests {C : ℕ} {p : Program C} {s : BitState C} {r : Result Bits C}
    (h : tick p s=some r) :
    requestCount r.events=(needsBit (p s.pc)).toNat ∧ r.state.source=s.source.drop (requestCount r.events) := by
  cases hp : p s.pc with
  | halt => simp [tick,hp] at h
  | move dst src pc =>
    simp only [tick,hp,Option.some.injEq] at h
    subst r
    simp [requestCount,needsBit]
  | make dst recipe pc =>
    simp only [tick,hp,Option.some.injEq] at h
    subst r
    simp [requestCount,needsBit,allocate]
  | branch src n z o pair =>
    simp only [tick,hp] at h
    split at h
    · simp at h
    · simp only [Option.some.injEq] at h
      subst r
      simp [requestCount,needsBit]
  | field dst src right pc =>
    simp only [tick,hp] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst r
      simp [requestCount,needsBit]
    · simp at h
  | call entry continuation dst =>
    simp only [tick,hp,Option.some.injEq] at h
    subst r
    simp [requestCount,needsBit]
  | ret src =>
    simp only [tick,hp] at h
    split at h
    · simp at h
    · simp only [Option.some.injEq] at h
      subst r
      simp [requestCount,needsBit]
  | request dst pc =>
    simp only [tick,hp,Option.some.injEq] at h
    subst r
    simp [requestCount,needsBit,allocate]
  | emit src pc =>
    simp only [tick,hp] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst r
      simp [requestCount,needsBit]
    · simp at h

def guardCost (C : ℕ) : ℕ := controlCost C + 4

def execute {C : ℕ} (p : Program C) : ℕ → BitState C → ℕ → Option (BitState C × ℕ)
  | 0,_,_ => none
  | fuel+1,s,paid =>
    if needsBit (p s.pc) = true ∧ s.source = [] then none
    else
      let r := attempt p s
      let paid := paid+r.operations+guardCost C
      match r.result with
      | none => some (s,paid)
      | some next => execute p fuel next.state paid

private theorem request_guard {C : ℕ} {p : Program C} {s : BitState C} {r : Result Bits C}
    (h : tick p s=some r) :
    needsBit (p s.pc)=true ∧ s.source=[] ↔ ¬ requestCount r.events ≤ s.source.length := by
  rw [(tick_requests h).1]
  cases needsBit (p s.pc) <;> cases s.source <;> simp

theorem execute_eq {C t q : ℕ} {p : Program C} {s u : BitState C} {events : List Event}
    (run : Run p t q s events u) (stop : (attempt p u).result=none) (fuel paid : ℕ) (enoughFuel : t<fuel) :
    execute p fuel s paid =
      if requestCount events ≤ s.source.length then
        some (u,paid+q+(attempt p u).operations+(t+1)*guardCost C)
      else none := by
  induction run generalizing fuel paid with
  | done s =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hn : needsBit (p s.pc)=false := by
        cases hp : p s.pc <;> simp [needsBit]
        rw [attempt_result] at stop
        simp [tick,hp] at stop
      simp [execute,hn,stop,requestCount]
  | @step s u r t q events hstep body ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have ht : (attempt p s).result=some r := (attempt_result p s).trans hstep
      have hguard := request_guard hstep
      have hs := (tick_requests hstep).2
      by_cases first : requestCount r.events ≤ s.source.length
      · have noBlock : ¬ (needsBit (p s.pc)=true ∧ s.source=[]) := fun h => (hguard.mp h) first
        have all : requestCount r.events+requestCount events ≤ s.source.length ↔
            requestCount events ≤ r.state.source.length := by
          rw [hs,List.length_drop]
          omega
        simp only [execute,noBlock,ite_false,ht,success_cost ht,count_append,all]
        rw [ih stop fuel _ (by omega)]
        have cost : paid+r.cost+guardCost C+q+(attempt p u).operations+(t+1)*guardCost C =
            paid+(r.cost+q)+(attempt p u).operations+(t+1+1)*guardCost C := by
          simp only [Nat.add_mul,Nat.one_mul]
          omega
        rw [cost]
      · have block : needsBit (p s.pc)=true ∧ s.source=[] := hguard.mpr first
        have noAll : ¬ requestCount (r.events++events) ≤ s.source.length := by
          rw [count_append]
          omega
        rw [execute,ite_eq_left block,ite_eq_right noAll]

end DirectedFlowCutGap.GuardedReferenceExecution
