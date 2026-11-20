import DirectedFlowCutGap.PaidTotalRawGraphExecution
import DirectedFlowCutGap.OriginalGraphCostEnvelope

/-! Polynomial scalar work of initial cache construction and the actual
fuel-free packed interpreter on the represented original graph. -/
namespace DirectedFlowCutGap.PaidTotalRawGraphExecution

open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal
open RetainedGridState (PairFlags)
open RawGraphControllerProgram (instructionBound)
open OriginalGraphCostEnvelope (Covered preparedCells packedCost)

private def Parameters := {v : ℕ × ℕ × ℕ // v.2.1 ≤ v.1}

private theorem magnitudes (n L T : ℕ) :
    let H := preparedCells n L T
    H+1≤packedCost n L T ∧ instructionBound n L (H+1) T.bits≤packedCost n L T := by
  let H := preparedCells n L T
  let steps := instructionBound n L (H+1) T.bits
  have extent : H+1≤packedCost n L T := by
    have hk : H≤H^3 := Nat.le_self_pow (by decide) H
    change H+1≤64*H^3+16+_
    omega
  let guard := GuardedReferenceExecution.guardCost 26704
  have one : 1≤guard := by decide
  have charge : (steps+1)*guard≤packedCost n L T := by
    unfold packedCost RawGraphControllerProgram.chargeBound
    dsimp only
    exact (Nat.le_add_left _ _).trans (Nat.le_add_left _ _)
  have step : steps≤(steps+1)*guard := by
    calc
      _ ≤ steps+1 := Nat.le_succ steps
      _ = (steps+1)*1 := (Nat.mul_one _).symm
      _ ≤ _ := Nat.mul_le_mul_left _ one
  exact ⟨extent,step.trans charge⟩

set_option maxHeartbeats 1800000 in
private theorem scalar_covered :
    Covered (fun x : Parameters => x.1.1+x.1.2.2) (fun x =>
      let H := preparedCells x.1.1 x.1.2.1 x.1.2.2
      scalarBudget (H+1) H (instructionBound x.1.1 x.1.2.1 (H+1) x.1.2.2.bits)) := by
  let width (x : Parameters) := x.1.1+x.1.2.2
  let packing (x : Parameters) := packedCost x.1.1 x.1.2.1 x.1.2.2
  let cells (x : Parameters) := preparedCells x.1.1 x.1.2.1 x.1.2.2
  let steps (x : Parameters) := instructionBound x.1.1 x.1.2.1 (cells x+1) x.1.2.2.bits
  have build : Covered width packing := by
    obtain ⟨p,cap⟩ := OriginalGraphCostEnvelope.bounded_trials_polynomial
    exact ⟨p,fun x => cap x.1.1 x.1.2.1 x.1.2.2 x.property⟩
  have H : Covered width cells := build.of_le fun x =>
    (Nat.le_succ (cells x)).trans (magnitudes x.1.1 x.1.2.1 x.1.2.2).1
  have K : Covered width steps := build.of_le fun x => (magnitudes x.1.1 x.1.2.1 x.1.2.2).2
  change Covered width (fun x => scalarBudget (cells x+1) (cells x) (steps x))
  simp only [scalarBudget,CachedBinaryAttempt.budget,CachedHeapWidths.readerWidth,CachedScalarRead.budget,
    CachedBinaryAttempt.sumsBudget,BinaryGuardedCacheExecution.additionBudget,stepBound]
  cover_arithmetic

open Polynomial in
theorem scalar_polynomial : ∃ p : Polynomial ℕ, ∀ (n L T : ℕ) (adj : PairFlags n)
    (initial : BitState 26704) (data : RawGraphControllerLaw.Input (L:=L) adj T.bits
      (preparedCells n L T+1) (preparedCells n L T) initial) (positive : 0<L), L≤n →
        (runWithScalars initial data positive).2≤p.eval (n+T) := by
  obtain ⟨p,cap⟩ := scalar_covered
  exact ⟨p,fun n L T _ initial data positive inside =>
    (scalar_paid initial data positive).trans (cap ⟨⟨n,L,T⟩,inside⟩)⟩

end DirectedFlowCutGap.PaidTotalRawGraphExecution
