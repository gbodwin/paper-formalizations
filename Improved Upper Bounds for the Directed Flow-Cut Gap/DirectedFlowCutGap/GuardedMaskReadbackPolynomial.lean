import DirectedFlowCutGap.GuardedFuelFreeRounding
import DirectedFlowCutGap.OriginalGraphCostEnvelope

/-! Polynomial metadata work for the actual final mask readback on every
literal random tape in the active positive-level rounding regime. -/
namespace DirectedFlowCutGap.GuardedFuelFreeRounding

open BinaryArithmetic ImmutableReferenceSimulation
open RetainedGridState (PairFlags)
open RawGraphControllerProgram (instructionBound)
open OriginalGraphCostEnvelope (preparedCells packedCost)

private theorem size_le_self (n : ℕ) : n.size≤n := Nat.size_le.mpr Nat.lt_two_pow_self

private theorem heap_index_width {H B : ℕ} (bounded : B≤H) :
    CachedHeapWidths.readerWidth H B≤64*(H+1)*(H+2) := by
  have Bwide : B≤H+1 := bounded.trans (Nat.le_succ H)
  have high : max B (H+1).size≤H+1 := max_le Bwide (size_le_self _)
  have shared : H+1≤64*(H+1)*(H+2) := by
    calc
      H+1 ≤ 64*(H+1) := by omega
      _ ≤ _ := Nat.le_mul_of_pos_right _ (by omega)
  unfold CachedHeapWidths.readerWidth
  exact max_le (Bwide.trans shared) ((size_le_self _).trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right high 1)))

private theorem work_mono {X Y : ℕ} (fits : X≤Y) :
    CachedScalarRead.budget X≤CachedScalarRead.budget Y := by
  unfold CachedScalarRead.budget
  gcongr

private theorem readback_scale (n L T : ℕ) :
    preparedCells n L T+1+(instructionBound n L (preparedCells n L T+1) T.bits+1) ≤ 2*packedCost n L T := by
  let H := preparedCells n L T
  let steps := instructionBound n L (H+1) T.bits+1
  have allocated : H+1≤packedCost n L T := by
    have square : H≤H^3 := Nat.le_self_pow (by decide) H
    change H+1 ≤ 64*H^3+16+_
    omega
  let guard := GuardedReferenceExecution.guardCost 26704
  have paid : steps*guard≤packedCost n L T := by
    unfold packedCost RawGraphControllerProgram.chargeBound
    dsimp only
    exact (Nat.le_add_left _ _).trans (Nat.le_add_left _ _)
  have guardPositive : 1≤guard := by decide
  have fuel : steps≤packedCost n L T :=
    ((Nat.mul_one steps).symm.le.trans (Nat.mul_le_mul_left steps guardPositive)).trans paid
  change H+1+steps ≤ 2*packedCost n L T
  omega

open Polynomial in
theorem hard_readback_polynomial : ∃ p : Polynomial ℕ,
    ∀ (n L T : ℕ) (adj : PairFlags n) (positive : 0<L) (tape : Bits), L≤n →
      (hardMeasured T adj L positive tape).2≤p.eval (n+T) := by
  obtain ⟨packing,covered⟩ := OriginalGraphCostEnvelope.bounded_trials_polynomial
  let h : Polynomial ℕ := 2*packing
  let width : Polynomial ℕ := 64*(h+1)*(h+2)
  refine ⟨h*(2*(128*(width+2)^2+6*(96*(width+2)^2+4)+48*(width+1)+20)),?_⟩
  intro n L T adj positive tape inside
  let H := preparedCells n L T
  let fuel := instructionBound n L (H+1) T.bits+1
  let M := 2*packing.eval (n+T)
  have memory : H+1+fuel≤M := (readback_scale n L T).trans (Nat.mul_le_mul_left 2 (covered n L T inside))
  have pointerFits : H+fuel≤H+1+fuel := by omega
  have widthFits : CachedHeapWidths.readerWidth (H+1+fuel) (H+fuel)≤64*(M+1)*(M+2) :=
    (heap_index_width pointerFits).trans (by gcongr)
  have read := hard_readback_paid T adj L positive tape
  simp only [h,width,eval_add,eval_mul,eval_pow,eval_ofNat,eval_one]
  change (hardMeasured T adj L positive tape).2≤M*(2*CachedScalarRead.budget (64*(M+1)*(M+2)))
  exact read.trans (Nat.mul_le_mul memory (Nat.mul_le_mul_left 2 (work_mono widthFits)))

end DirectedFlowCutGap.GuardedFuelFreeRounding
