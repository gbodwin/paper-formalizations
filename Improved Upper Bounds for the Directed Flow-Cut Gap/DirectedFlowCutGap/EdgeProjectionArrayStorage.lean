import DirectedFlowCutGap.PhysicalLineStorage
import DirectedFlowCutGap.BinaryEdgeProjection

/-! Array constructions in the original fractional-row, cut and witness
projections. Retained inputs are shared by reference in this model. -/
namespace DirectedFlowCutGap.EdgeProjectionArrayStorage

open BinaryArrayNestedStorage (Grid WithChildren schedule gridSchedule flat_schedule grid_schedule)
open BinaryEdgeProjection EncodedEdgeLineInput
open RetainedGridState (Flags PairFlags)
open FractionalCoverRawCore (RawRow)

theorem input_arrays {n : ℕ} (D : Input n) (row : RawRow (lineSize n)) :
    Grid (roundingInputWithControl D row).1.1.weights (gridSchedule n n) := by
  unfold roundingInputWithControl
  apply grid_schedule
  intro i
  apply BinaryArrayBatch.runWithChildWork_storage

theorem output_cut_arrays {n : ℕ} (D : Input n) (mask : Flags (lineSize n)) :
    Grid (toEdgesWithControl D mask).1.1 (gridSchedule n n) := by
  unfold toEdgesWithControl
  apply grid_schedule
  intro i
  apply BinaryArrayBatch.runWithChildWork_storage

theorem line_label_array (n : ℕ) : WithChildren (BinaryLineLabels.labelsWithControl n).1.1 (fun _ => [])
    (schedule (lineSize n) (fun _ => [])) := by
  apply flat_schedule
  unfold BinaryLineLabels.labelsWithControl
  apply BinaryArrayBatch.run_storage

theorem line_mask_array {n : ℕ} (mask : PairFlags n) : WithChildren (toLineWithControl mask).1.1 (fun _ => [])
    (schedule (lineSize n) (fun _ => [])) := by
  apply flat_schedule
  unfold toLineWithControl
  apply BinaryArrayBatch.runWithChildWork_storage

theorem pullback_arrays {n : ℕ} {D : EncodedEdgeGadget.Input n} (g : EncodedEdgeGadget.Prepared D)
    (mask : Flags g.size) : ∃ arcs : PairFlags n,
      Grid arcs (gridSchedule n n) ∧
      (pullbackWithControl g mask).1.1=(toLineWithControl arcs).1.1 ∧
      WithChildren (toLineWithControl arcs).1.1 (fun _ => []) (schedule (lineSize n) (fun _ => [])) := by
  unfold pullbackWithControl
  refine ⟨_,?_,rfl,line_mask_array _⟩
  apply grid_schedule
  intro i
  apply BinaryArrayBatch.runWithChildWork_storage

theorem output_arrays {n : ℕ} (D : Input n) (output : EncodedVertexSolver.Output (lineSize n)) :
    match output with
    | .cut mask => Grid (toEdgesWithControl D mask).1.1 (gridSchedule n n)
    | .infeasible _ => WithChildren (BinaryLineLabels.labelsWithControl n).1.1 (fun _ => [])
        (schedule (lineSize n) (fun _ => []))
    | .invalid => True := by
  cases output with
  | cut mask => exact output_cut_arrays D mask
  | infeasible _ => exact line_label_array n
  | invalid => trivial

end DirectedFlowCutGap.EdgeProjectionArrayStorage
