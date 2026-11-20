import DirectedFlowCutGap.EdgeGadgetArrayStorage
import DirectedFlowCutGap.EdgeProjectionArrayStorage
import DirectedFlowCutGap.PaidDirectEdgeWire

/-! Every reached edge round reserves its fractional row and gadget arrays.
Cut projection reserves its arrays only after the literal round succeeds. -/
namespace DirectedFlowCutGap.EdgeRoundStorage

open BinaryArithmetic EncodedArrayStorage EncodedEdgeLineInput Polynomial
open BinaryArrayNestedStorage (Code Grid WithChildren gridSchedule schedule flat_schedule flat_bounds grid_bounds
  copyBudget copyBudget_eval copyBudget_mono cellBudget cellBudget_eval cellBudget_mono)
open BinaryEdgeProjection (roundingInputWithControl toLineWithControl pullbackWithControl)
open FractionalCoverRawCore (RawRow)
open RetainedGridState (Flags PairFlags)

def projectionCode (n k : ℕ) : Code :=
  let line := schedule (lineSize n) (fun _ => [])
  schedule k (fun _ => [])++gridSchedule n n++line++line

def roundCode {n : ℕ} (D : Input n) (mode : ChargedVertexModes.Mode) (T : ℕ)
    (row : RawRow (lineSize n)) (tape : Bits) : Code :=
  let input := (roundingInputWithControl D row).1.1
  let g := (BinaryEdgeGadget.buildWithControl input).1.1
  let run := PaidVertexRounding.runner mode T g.data tape
  gridSchedule n n++EdgeGadgetArrayStorage.codeFor n g.size++
    (if run.1.isSome then projectionCode n g.size else [])

theorem observed_round {n : ℕ} (D : Input n) (mode : ChargedVertexModes.Mode) (T : ℕ)
    (r : EncodedVertexSolver.RoundingInput (lineSize n)) (tape : Bits) :
    let input := (roundingInputWithControl D r.weights).1.1
    let g := (BinaryEdgeGadget.buildWithControl input).1.1
    let draw := PaidVertexRounding.runner mode T g.data tape
    (PaidDirectEdgeWire.roundWithGadgetControl D mode T r tape).1.1.map (fun c => (c.mask,c.suffix)) =
      draw.1.map (fun c => ((pullbackWithControl g c.mask).1.1,c.suffix)) := by
  dsimp only
  have ordinary := congrFun (congrFun (congrFun (PaidDirectEdgeWire.round_value D mode) T) r) tape
  rw [PaidDirectEdgeWire.roundWithGadgetControl_reference,ordinary]
  simp only [PhysicalAmplifiedBinaryEdge.round,PhysicalAmplifiedBinaryEdge.roundOn,BinaryEdgeProjection.roundingInput,
    PaidVertexRounding.runner_value,Option.map_map,Function.comp_def,PhysicalVertexRounding.project,BinaryEdgeProjection.pullback]
  have gadget := congrArg Prod.fst (BinaryEdgeGadget.build_control_projection (roundingInputWithControl D r.weights).1.1)
  change (BinaryEdgeGadget.buildWithControl (roundingInputWithControl D r.weights).1.1).1.1 =
    (BinaryEdgeGadget.build (roundingInputWithControl D r.weights).1.1).1 at gadget
  rw [gadget]

theorem round_arrays {n : ℕ} (D : Input n) (mode : ChargedVertexModes.Mode) (T : ℕ)
    (row : RawRow (lineSize n)) (tape : Bits) :
    let input := (roundingInputWithControl D row).1.1
    let g := (BinaryEdgeGadget.buildWithControl input).1.1
    let draw := PaidVertexRounding.runner mode T g.data tape
    Grid input.weights (gridSchedule n n) ∧
    match draw.1 with
    | none => roundCode D mode T row tape=gridSchedule n n++EdgeGadgetArrayStorage.codeFor n g.size
    | some cut =>
      WithChildren (BinaryArrayBatch.run (fun i : Fin g.size => (i,0))).1.1 (fun _ => [])
        (schedule g.size (fun _ => [])) ∧
      WithChildren (BinaryLineLabels.labelsWithControl n).1.1 (fun _ => [])
        (schedule (lineSize n) (fun _ => [])) ∧
      (∃ arcs : PairFlags n, Grid arcs (gridSchedule n n) ∧
        (pullbackWithControl g cut.mask).1.1=(toLineWithControl arcs).1.1 ∧
        WithChildren (toLineWithControl arcs).1.1 (fun _ => []) (schedule (lineSize n) (fun _ => []))) ∧
      roundCode D mode T row tape=gridSchedule n n++EdgeGadgetArrayStorage.codeFor n g.size++projectionCode n g.size := by
  dsimp only
  refine ⟨EdgeProjectionArrayStorage.input_arrays D row,?_⟩
  let input := (roundingInputWithControl D row).1.1
  let g := (BinaryEdgeGadget.buildWithControl input).1.1
  have shape : roundCode D mode T row tape=gridSchedule n n++EdgeGadgetArrayStorage.codeFor n g.size++
      (if (PaidVertexRounding.runner mode T g.data tape).1.isSome then projectionCode n g.size else []) := rfl
  cases h : (PaidVertexRounding.runner mode T g.data tape).1 with
  | none =>
    change roundCode D mode T row tape=gridSchedule n n++EdgeGadgetArrayStorage.codeFor n g.size
    rw [shape,h]
    simp only [Option.isSome_none,Bool.false_eq_true,ite_false,List.append_nil]
  | some cut =>
    refine ⟨flat_schedule (BinaryArrayBatch.run_storage _),EdgeProjectionArrayStorage.line_label_array n,
      EdgeProjectionArrayStorage.pullback_arrays g cut.mask,?_⟩
    change roundCode D mode T row tape=gridSchedule n n++EdgeGadgetArrayStorage.codeFor n g.size++projectionCode n g.size
    simp only [shape,h,Option.isSome_some,ite_true]

theorem polynomial : ∃ cells copies : Polynomial ℕ,
    ∀ {n : ℕ} (D : Input n) (mode : ChargedVertexModes.Mode) (T : ℕ)
      (row : RawRow (lineSize n)) (tape : Bits),
      let code := roundCode D mode T row tape
      fresh code ≤ cells.eval n ∧ code.length ≤ copies.eval n := by
  obtain ⟨gadgetCells,gadgetCopies,gadgetBounds⟩ := EdgeGadgetArrayStorage.bounds
  let dim := BinaryEdgeGadget.dimension (X : Polynomial ℕ)
  let line : Polynomial ℕ := X*2+X*X
  let cells := gadgetCells+2*((X+1)*cellBudget X)+cellBudget dim+2*cellBudget line
  let copies := gadgetCopies+2*((X+1)*copyBudget X)+copyBudget dim+2*copyBudget line
  refine ⟨cells,copies,?_⟩
  intro n D mode T row tape
  let input := (roundingInputWithControl D row).1.1
  let g := (BinaryEdgeGadget.buildWithControl input).1.1
  let seen := PaidVertexRounding.runner mode T g.data tape
  let before := gridSchedule n n++EdgeGadgetArrayStorage.codeFor n g.size
  let after := projectionCode n g.size
  have size : g.size ≤ dim.eval n := by
    rw [show g=(BinaryEdgeGadget.build input).1 from congrArg Prod.fst (BinaryEdgeGadget.build_control_projection input)]
    simp only [dim,BinaryEdgeGadget.dimension,eval_add,eval_mul,eval_X,eval_ofNat]
    exact BinaryEdgeGadget.size_le input
  have lineSizeEq : line.eval n=lineSize n := by simp only [line,lineSize,eval_mul,eval_add,eval_X,eval_ofNat]
  have labels := flat_bounds (lineSize n)
  have grid := grid_bounds n
  have gBound : fresh (EdgeGadgetArrayStorage.codeFor n g.size) ≤ gadgetCells.eval n ∧
      (EdgeGadgetArrayStorage.codeFor n g.size).length ≤ gadgetCopies.eval n := gadgetBounds input
  have hCells := (flat_bounds g.size).2.trans (cellBudget_mono size)
  have hCopies := (flat_bounds g.size).1.trans (copyBudget_mono size)
  have full : fresh (before++after) ≤ cells.eval n ∧ (before++after).length ≤ copies.eval n := by
    simp only [before,after,projectionCode,fresh_append,List.length_append,cells,copies,eval_add,eval_mul,
      eval_ofNat,eval_one,eval_X,cellBudget_eval,copyBudget_eval,lineSizeEq]
    constructor <;> omega
  cases h : seen.1 with
  | none =>
    change fresh (before++(if seen.1.isSome then after else [])) ≤ cells.eval n ∧
      (before++(if seen.1.isSome then after else [])).length ≤ copies.eval n
    simp only [h,Option.isSome_none,Bool.false_eq_true,ite_false,List.append_nil]
    exact ⟨(Nat.le_add_right (fresh before) (fresh after)).trans (by simpa only [fresh_append] using full.1),
      (Nat.le_add_right before.length after.length).trans (by simpa only [List.length_append] using full.2)⟩
  | some cut =>
    change fresh (before++(if seen.1.isSome then after else [])) ≤ cells.eval n ∧
      (before++(if seen.1.isSome then after else [])).length ≤ copies.eval n
    simpa only [h,Option.isSome_some,ite_true] using full

end DirectedFlowCutGap.EdgeRoundStorage
