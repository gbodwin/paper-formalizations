import DirectedFlowCutGap.TotalGuardedPackedExecution
import DirectedFlowCutGap.RawGraphInputStore

/-! Each represented original graph gives an accessible guarded state.
The finite instruction bound appears in the proof of agreement. The total
runner executes to halt or exhaustion. -/
namespace DirectedFlowCutGap.TotalRawGraphExecution

open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal RetainedGridState
open OriginalGraphControllerLaw (epochs ratio)
open RawGraphControllerProgram (program state instructionBound)
open CachedReferenceExecution (FastState)
open PhysicalControllerInitializer (initialCode)

private theorem available {n L H A : ℕ} {adj : PairFlags n} {trials : Bits} {initial : BitState 26704}
    (data : RawGraphControllerLaw.Input (L:=L) adj trials H A initial) (positive : 0<L) :
    Acc (TotalGuardedPackedExecution.Next program) (FastState.ofReference initial) := by
  let old := eraseState initial
  let F := CandidateEnumeration.make n L
  let EN := F.nodes.enumeration
  let E := F.network.enumeration
  have before : old=state old.heap old.registers [] initial.source 0 := by
    have quiet := data.quiet
    have entry := data.entry
    have dense := data.dense
    cases initial
    simp_all [old,eraseState,State.map,ReferenceProgramInvocation.state]
  have heap : old.heap.length ≤ H := by
    have bound := data.bounded.1
    simp only [State.records] at bound
    have len : initial.heap.length ≤ H := by omega
    simpa only [old,eraseState,State.map,List.length_map] using len
  have traces := RawGraphControllerProgram.natural_cut positive EN E heap data.graph data.trials initial.source
  cases model : ControllerTapeModel.run positive E (ratio n) (value trials) (epochs n) (epochs n)
      (initialCode adj positive) initial.source with
  | none =>
    rw [model] at traces
    obtain ⟨_,_,_,trace,short⟩ := traces
    rw [← before] at trace
    obtain ⟨_,_,ran,_,_,_,_⟩ := polynomial_simulation data.bounded trace
    exact TotalGuardedPackedExecution.ready_of_run ran (Or.inr short) (CachedReferenceExecution.freeze_ofReference _)
  | some answer =>
    rcases answer with ⟨cut,rest,used⟩
    rw [model] at traces
    obtain ⟨ext,out,_,_,trace,_,_,_,_⟩ := traces
    rw [← before] at trace
    have halted : tickNatural program (state (old.heap++ext) out [] rest 6)=none := rfl
    obtain ⟨_,_,ran,_,stop,_,_⟩ := terminating_simulation data.bounded trace halted
    exact TotalGuardedPackedExecution.ready_of_run ran (Or.inl stop) (CachedReferenceExecution.freeze_ofReference _)

def run {n L H A : ℕ} {adj : PairFlags n} {trials : Bits} (initial : BitState 26704)
    (data : RawGraphControllerLaw.Input (L:=L) adj trials H A initial) (positive : 0<L) :
    Option (FastState 26704 × ℕ) :=
  TotalGuardedPackedExecution.execute program ⟨FastState.ofReference initial,available data positive⟩ 0

private theorem cache_none {initial : BitState 26704} {fuel : ℕ}
    (failed : GuardedReferenceExecution.execute program fuel initial 0=none) :
    CachedGuardedReferenceExecution.execute program fuel (FastState.ofReference initial) 0=none := by
  have h := CachedGuardedReferenceExecution.execute_ofReference program fuel initial 0
  rw [failed] at h
  exact Option.map_eq_none_iff.mp h

set_option maxHeartbeats 1200000 in
theorem run_eq {n L H A : ℕ} {adj : PairFlags n} {trials : Bits} (initial : BitState 26704)
    (data : RawGraphControllerLaw.Input (L:=L) adj trials H A initial) (positive : 0<L) :
    run initial data positive =
      CachedGuardedReferenceExecution.execute program (instructionBound n L H trials+1) (FastState.ofReference initial) 0 := by
  let F := CandidateEnumeration.make n L
  let EN := F.nodes.enumeration
  let E := F.network.enumeration
  let bound := instructionBound n L H trials+1
  let start : TotalGuardedPackedExecution.Ready program := ⟨FastState.ofReference initial,available data positive⟩
  have ref := RawGraphControllerProgram.guarded_cut positive EN E initial data.bounded data.entry
    data.quiet data.dense data.graph data.trials
  change TotalGuardedPackedExecution.execute program start 0 =
    CachedGuardedReferenceExecution.execute program bound start.1 0
  cases model : ControllerTapeModel.run positive E (ratio n) (value trials) (epochs n) (epochs n)
      (initialCode adj positive) initial.source with
  | none =>
    rw [model] at ref
    change ∀ fuel paid, GuardedReferenceExecution.execute program fuel initial paid=none at ref
    obtain ⟨fuel,cached⟩ := TotalGuardedPackedExecution.eventual program start 0
    rw [← cached]
    exact (cache_none (ref fuel 0)).trans (cache_none (ref bound 0)).symm
  | some answer =>
    rcases answer with ⟨cut,rest,used⟩
    rw [model] at ref
    obtain ⟨out,paid,ran,_,_,_,_,_,_⟩ := ref
    have matchBound := (CachedGuardedReferenceExecution.execute_ofReference program bound initial 0).trans ran
    change (CachedGuardedReferenceExecution.execute program bound start.1 0).map _=some (out,paid) at matchBound
    cases actual : CachedGuardedReferenceExecution.execute program bound start.1 0 with
    | none => simp only [actual,Option.map_none,reduceCtorEq] at matchBound
    | some got => exact TotalGuardedPackedExecution.matches_some program bound start 0 actual

end DirectedFlowCutGap.TotalRawGraphExecution
