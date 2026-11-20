import DirectedFlowCutGap.PaidCacheTrace
import DirectedFlowCutGap.PaidTotalGuardedExecution
import DirectedFlowCutGap.RawGraphControllerProgram
import DirectedFlowCutGap.RawGraphControllerLaw
import DirectedFlowCutGap.ReferenceSourcePadding

/-! The complete packed trace on a proof-only zero extension supplies a
fuel bound for the original literal source. The executable takes only the
original state and an erased termination certificate. -/
namespace DirectedFlowCutGap.PaidTotalRawGraphExecution

open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal RetainedGridState
open OriginalGraphControllerLaw (epochs ratio readBound tape_complete)
open RawGraphControllerProgram (program instructionBound)
open CachedReferenceExecution (FastState)
open PhysicalControllerInitializer (initialCode)
open ReferenceSourcePadding (withSource)

set_option maxHeartbeats 1800000 in
theorem complete_halted_trace {n L H A : ℕ} {adj : PairFlags n} {trials : Bits} {initial : BitState 26704}
    (data : RawGraphControllerLaw.Input (L:=L) adj trials H A initial) (positive : 0<L) :
    ∃ steps ≤ instructionBound n L H trials, ∃ operations events out,
      Run program steps operations initial events out ∧ program out.pc=.halt := by
  let extra := readBound n L (value trials)
  let extended := initial.source++List.replicate extra false
  let padded := withSource initial extended
  let F := CandidateEnumeration.make n L
  let EN := F.nodes.enumeration
  let E := F.network.enumeration
  have enough : extra ≤ extended.length := by simp [extended]
  obtain ⟨out,reads,found,_⟩ := tape_complete (adj:=adj) positive E (value trials) extended enough
  have success := RawGraphControllerProgram.guarded_cut positive EN E padded
    data.bounded data.entry data.quiet data.dense data.graph data.trials
  rw [show padded.source=extended from rfl,found] at success
  obtain ⟨finish,charge,observed,_,_,pc,_,_,_⟩ := success
  obtain ⟨k,within,operations,events,low,_⟩ := PaidTotalGuardedExecution.trace_of_success observed
  have trimmed := ReferenceSourcePadding.trim low initial.source extra rfl
  have initial_eq : withSource padded initial.source=initial := by cases initial; rfl
  rw [initial_eq] at trimmed
  refine ⟨k,Nat.le_of_lt_succ within,operations,events,_,trimmed,?_⟩
  have terminal : program (withSource finish (initial.source.drop (ReferenceSourcePadding.requests events))).pc=.halt := by
    change program finish.pc=.halt
    rw [pc]
    rfl
  exact terminal

theorem complete_trace {n L H A : ℕ} {adj : PairFlags n} {trials : Bits} {initial : BitState 26704}
    (data : RawGraphControllerLaw.Input (L:=L) adj trials H A initial) (positive : 0<L) :
    ∃ steps ≤ instructionBound n L H trials, ∃ operations events out,
      Run program steps operations initial events out ∧ tick program out=none := by
  obtain ⟨steps,within,operations,events,out,trace,halt⟩ := complete_halted_trace data positive
  exact ⟨steps,within,operations,events,out,trace,by rw [tick,halt]⟩

private theorem ready {n L H A : ℕ} {adj : PairFlags n} {trials : Bits} {initial : BitState 26704}
    (data : RawGraphControllerLaw.Input (L:=L) adj trials H A initial) (positive : 0<L) :
    Acc (TotalGuardedPackedExecution.Next program) (FastState.ofReference initial) := by
  obtain ⟨steps,_,work,events,out,trace,halt⟩ := complete_trace data positive
  exact TotalGuardedPackedExecution.ready_of_run trace
    (Or.inl ((ImmutableReferenceTerminal.attempt_result program out).trans halt))
    (CachedReferenceExecution.freeze_ofReference initial)

def run {n L H A : ℕ} {adj : PairFlags n} {trials : Bits} (initial : BitState 26704)
    (data : RawGraphControllerLaw.Input (L:=L) adj trials H A initial) (positive : 0<L) :
    Option (FastState 26704) × ℕ :=
  PaidTotalGuardedExecution.execute program ⟨FastState.ofReference initial,ready data positive⟩ 0

theorem run_eq {n L H A : ℕ} {adj : PairFlags n} {trials : Bits} (initial : BitState 26704)
    (data : RawGraphControllerLaw.Input (L:=L) adj trials H A initial) (positive : 0<L) :
    run initial data positive=PaidGuardedExecution.execute program (instructionBound n L H trials+1)
      (FastState.ofReference initial) 0 := by
  obtain ⟨k,within,work,events,out,trace,halt⟩ := complete_trace data positive
  unfold run
  exact PaidTotalGuardedExecution.matches_trace trace halt _ (CachedReferenceExecution.freeze_ofReference initial)
    (instructionBound n L H trials+1) 0 (Nat.lt_succ_of_le within)

/-- Cumulative persistent-array traffic of the actual guarded packed run.
The walked prefix stops at the first unavailable request or the proved halt. -/
theorem storage_traffic {n L H A : ℕ} {adj : PairFlags n} {trials : Bits} (initial : BitState 26704)
    (data : RawGraphControllerLaw.Input (L:=L) adj trials H A initial) (positive : 0<L) :
    ∃ steps ≤ instructionBound n L H trials, ∃ cells copies stop,
      PaidCacheTrace.Walk program (FastState.ofReference initial) steps cells copies stop ∧
      stop.freeze.Bounded (H+steps) (A+steps) ∧
      cells ≤ steps*(3*(H+steps)+11) ∧ copies ≤ steps*(12*(H+steps)+23) ∧
      match (run initial data positive).1 with
      | none => TotalGuardedPackedExecution.blocked program stop
      | some final => final=stop ∧ program stop.pc=.halt := by
  obtain ⟨k,limit,ops,events,out,trace,halt⟩ := complete_halted_trace data positive
  let start : TotalGuardedPackedExecution.Ready program := ⟨FastState.ofReference initial,ready data positive⟩
  have initialShape := CachedReferenceExecution.freeze_ofReference initial
  obtain ⟨steps,within,cells,copies,stop,walk,observed⟩ := PaidCacheTrace.run_walk trace halt start initialShape 0
  have initialFits : start.1.freeze.Bounded H A := by rw [show start.1.freeze=initial from initialShape]; exact data.bounded
  obtain ⟨stopFits,allocated,instructions⟩ := walk.bounded initialFits
  rw [show run initial data positive=PaidTotalGuardedExecution.execute program start 0 from rfl]
  refine ⟨steps,within.trans limit,cells,copies,stop,walk,stopFits,allocated,instructions,?_⟩
  cases result : (PaidTotalGuardedExecution.execute program start 0).1 <;>
    simpa only [result] using observed

end DirectedFlowCutGap.PaidTotalRawGraphExecution
