import DirectedFlowCutGap.CachedGuardedReferenceExecution
import DirectedFlowCutGap.BinaryArithmetic

/-! Preserve incurred work when the guarded instruction interpreter runs out
of tape or fuel. Successful execution agrees with the existing cached entry. -/
namespace DirectedFlowCutGap.PaidGuardedExecution

open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal
open CachedReferenceExecution (FastState FastAttempt FastResult)
open GuardedReferenceExecution (needsBit guardCost)

def execute {C : ℕ} (program : Program C) : ℕ → FastState C → ℕ → Option (FastState C) × ℕ
  | 0, _, paid => (none,paid)
  | fuel+1,state,paid =>
      if needsBit (program state.pc)=true ∧ state.source=[] then (none,paid+guardCost C)
      else match CachedReferenceExecution.attempt program state with
        | .stopped final work => (some final,paid+work+guardCost C)
        | .completed step => execute program fuel step.state (paid+step.cost+guardCost C)

theorem observation {C : ℕ} (program : Program C) (fuel : ℕ) (state : FastState C) (paid : ℕ) :
    let r := execute program fuel state paid
    r.1.map (fun out => (out,r.2))=CachedGuardedReferenceExecution.execute program fuel state paid := by
  induction fuel generalizing state paid with
  | zero => rfl
  | succ fuel ih =>
      simp only [execute,CachedGuardedReferenceExecution.execute]
      split
      · rfl
      · split
        · rename_i final work stopped
          simp only [stopped,Option.map_some]
        · rename_i step performed
          rw [performed]
          exact ih _ _

def budget (C H B fuel : ℕ) : ℕ :=
  fuel*(stepBound C (H+fuel) (B+fuel)+guardCost C)

private theorem stepBound_mono {C H B K W : ℕ} (heap : H≤K) (width : B≤W) :
    stepBound C H B≤stepBound C K W := by unfold stepBound; gcongr

private theorem reference_step {C : ℕ} (program : Program C) (state : FastState C) (step : FastResult C)
    (performed : CachedReferenceExecution.attempt program state=.completed step) :
    tick program state.freeze=some step.freeze := by
  have matchStep := CachedReferenceExecution.attempt_eq program state
  rw [performed] at matchStep
  exact ((attempt_result program state.freeze).symm.trans (congrArg Attempt.result matchStep).symm)

theorem paid_le {C H B : ℕ} (program : Program C) (fuel : ℕ) (state : FastState C) (paid : ℕ)
    (fits : state.freeze.Bounded H B) :
    (execute program fuel state paid).2≤paid+budget C H B fuel := by
  induction fuel generalizing H B state paid with
  | zero => simp [execute,budget]
  | succ fuel ih =>
      let one := stepBound C (H+(fuel+1)) (B+(fuel+1))+guardCost C
      have larger := stepBound_mono (C:=C) (Nat.le_add_right H (fuel+1)) (Nat.le_add_right B (fuel+1))
      have whole : budget C H B (fuel+1)=fuel*one+one := by
        simp only [budget,one,Nat.add_mul,Nat.one_mul]
      have padding : guardCost C≤one := Nat.le_add_left _ _
      rw [execute,whole]
      split
      · change paid+guardCost C≤paid+(fuel*one+one)
        omega
      · have matchStep := CachedReferenceExecution.attempt_eq program state
        split
        · rename_i final work stopped
          have work_eq : work=(attempt program state.freeze).operations := by
            rw [stopped] at matchStep
            exact congrArg Attempt.operations matchStep
          have cost := (attempt_bound (p:=program) fits).trans larger
          change paid+work+guardCost C≤paid+(fuel*one+one)
          rw [work_eq]
          dsimp only [one]
          omega
        · rename_i step performed
          obtain ⟨growth,cost⟩ := tick_controlled fits (reference_step program state step performed)
          have subsequent := ih step.state (paid+step.cost+guardCost C) growth
          have nextBudget : budget C (H+1) (B+1) fuel=fuel*one := by
            unfold budget one
            rw [show H+1+fuel=H+(fuel+1) by omega,show B+1+fuel=B+(fuel+1) by omega]
          rw [nextBudget] at subsequent
          have work : step.cost≤stepBound C H B := cost
          have charge : step.cost+guardCost C≤one := Nat.add_le_add_right (work.trans larger) _
          exact subsequent.trans (by omega)

theorem returned_bounded {C H B : ℕ} (program : Program C) (fuel : ℕ) (state : FastState C) (paid : ℕ)
    (fits : state.freeze.Bounded H B) {final : FastState C}
    (ran : (execute program fuel state paid).1=some final) : final.freeze.Bounded (H+fuel) (B+fuel) := by
  induction fuel generalizing H B state paid with
  | zero => cases ran
  | succ fuel ih =>
      rw [execute] at ran
      split at ran
      · cases ran
      · split at ran
        · rename_i out work performed
          have same : out=state := CachedReferenceExecution.stopped_state program performed
          have returned := Option.some.inj ran
          subst final
          rw [same]
          exact fits.mono (Nat.le_add_right _ _) (Nat.le_add_right _ _)
        · rename_i step performed
          have grew := (tick_controlled fits (reference_step program state step performed)).1
          simpa only [Nat.add_right_comm H 1 fuel,Nat.add_right_comm B 1 fuel,Nat.add_assoc] using ih _ _ grew ran

private def executeBinaryAux {C : ℕ} (program : Program C) (fuel : Bits) (state : FastState C)
    (paid control : ℕ) :
    (Option (FastState C) × ℕ) × ℕ :=
  let zero := isZero fuel
  if empty : zero.1=true then ((none,paid),control+zero.2+4)
  else if needsBit (program state.pc)=true ∧ state.source=[] then ((none,paid+guardCost C),control+zero.2+8)
  else match CachedReferenceExecution.attempt program state with
    | .stopped final work => ((some final,paid+work+guardCost C),control+zero.2+8)
    | .completed step =>
        let pred := predCore fuel
        executeBinaryAux program pred.1 step.state (paid+step.cost+guardCost C) (control+zero.2+pred.2+8)
termination_by value fuel
decreasing_by
  have positive := Nat.pos_of_ne_zero (fun h => empty ((isZero_spec fuel).1.mpr h))
  have smaller := (predCore_spec fuel).1 positive
  change value (predCore fuel).1 < value fuel
  omega

private theorem binaryAux_spec {C : ℕ} (program : Program C) (fuel : Bits) (state : FastState C)
    (paid control : ℕ) :
    (executeBinaryAux program fuel state paid control).1=execute program (value fuel) state paid ∧
      (executeBinaryAux program fuel state paid control).2≤control+24*(value fuel+1)*(fuel.length+1) := by
  induction hv : value fuel using Nat.strong_induction_on generalizing fuel state paid control with
  | h n ih =>
      rw [← hv,executeBinaryAux]
      have zero := isZero_spec fuel
      by_cases empty : (isZero fuel).1=true
      · have h := zero.1.mp empty
        simp only [dite_eq_left empty,h,execute,Nat.zero_add,Nat.mul_one,true_and]
        omega
      · have positive := Nat.pos_of_ne_zero (fun h => empty (zero.1.mpr h))
        rw [dite_eq_right empty]
        obtain ⟨pred,short,cost⟩ := predCore_spec fuel
        have width := pred positive
        have next : value fuel=value (predCore fuel).1+1 := width.symm
        rw [next,execute]
        have one : 1≤value (predCore fuel).1+1+1 := by omega
        have cover : 24*(fuel.length+1)≤24*(value (predCore fuel).1+1+1)*(fuel.length+1) :=
          Nat.mul_le_mul (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left 24 one) (Nat.le_refl _)
        split
        · simp only [true_and]
          omega
        · split
          · rename_i final work performed
            simp only [true_and]
            omega
          · rename_i step performed
            have count := ih (value (predCore fuel).1) (by omega) (predCore fuel).1 step.state
              (paid+step.cost+guardCost C) (control+(isZero fuel).2+(predCore fuel).2+8) rfl
            simp only [count.1,true_and]
            have bound := count.2.trans (Nat.add_le_add_left
              (Nat.mul_le_mul_left _ (Nat.add_le_add_right short 1)) _)
            have add : 24*(value (predCore fuel).1+1+1)*(fuel.length+1)=
                24*(value (predCore fuel).1+1)*(fuel.length+1)+24*(fuel.length+1) := by ring
            rw [add]
            omega

/-- Decrement the actual binary fuel and retain its charge separately from
the instruction interpreter's charge. -/
def executeBinary {C : ℕ} (program : Program C) (fuel : Bits) (state : FastState C) (paid : ℕ) :
    (Option (FastState C) × ℕ) × ℕ :=
  executeBinaryAux program fuel state paid 0

theorem binary_spec {C : ℕ} (program : Program C) (fuel : Bits) (state : FastState C) (paid : ℕ) :
    (executeBinary program fuel state paid).1=execute program (value fuel) state paid ∧
      (executeBinary program fuel state paid).2≤24*(value fuel+1)*(fuel.length+1) := by
  simpa only [executeBinary,Nat.zero_add] using binaryAux_spec program fuel state paid 0

end DirectedFlowCutGap.PaidGuardedExecution
