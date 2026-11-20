import DirectedFlowCutGap.FramedSolverStackLayout
import DirectedFlowCutGap.FramedProjectedRoundWork

/-! Combine the recorded work, the modeled data arrays, and the modeled
frame reservations of the explicit-stack original source variants. -/
namespace DirectedFlowCutGap.FramedStackReservationWork

open BinaryArithmetic Polynomial
open BinaryArrayNestedStorage (Code)
open FramedChargedReservations (budget reservationWork reservations_le)
open PhysicalIntegerRoundingCost (eval_mono)

set_option maxHeartbeats 1000000 in
theorem vertex : ∃ p : Polynomial ℕ,
    ∀ (κ heap stack : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits),
      let solver := PaidFramedVertexWire.vertexWithTerminalFrameStackWork κ mode source tape
      ∃ post rounds : Code, FramedVertexPackedLayout.Prefix source post ∧
        FramedVertexPackedLayout.ModelWith RunnerProjectionLayout.Model κ mode source tape rounds ∧
        let data := PhysicalSourceInputJoin.vertexArrayCode source++post++rounds
        let frames := FramedSolverStackLayout.vertex κ mode source tape
        solver.1.2+solver.2.1+solver.2.2+reservationWork heap data+reservationWork stack frames ≤
          p.eval (source.length+κ+heap.size+stack.size) := by
  obtain ⟨base,recorded⟩ := FramedProjectedRoundWork.vertex
  obtain ⟨cells,steps,stacked⟩ := FramedSolverStackLayout.vertex_polynomial
  refine ⟨base+budget 0 cells steps,?_⟩
  intro κ heap stack mode source tape
  obtain ⟨post,rounds,prefixModel,roundModel,work⟩ := recorded κ heap mode source tape
  obtain ⟨frameSpace,frameSteps⟩ := stacked κ mode source tape
  have frames := reservations_le cells steps (source.length+κ) stack
    (FramedSolverStackLayout.vertex κ mode source tape) frameSpace frameSteps
  let x := source.length+κ+heap.size+stack.size
  have heapWidth : source.length+κ+heap.size ≤ x := Nat.le_add_right _ _
  have stackWidth : source.length+κ+stack.size ≤ x := by dsimp only [x]; omega
  refine ⟨post,rounds,prefixModel,roundModel,?_⟩
  simp only [PaidFramedVertexWire.vertex_terminal_frame_stack_reference,eval_add]
  exact Nat.add_le_add (work.trans (eval_mono _ heapWidth)) (frames.trans (eval_mono _ stackWidth))

set_option maxHeartbeats 1000000 in
theorem edge : ∃ p : Polynomial ℕ,
    ∀ (κ heap stack : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits),
      let solver := PaidDirectEdgeWire.edgeWithTerminalFrameStackWork κ mode source tape
      let input := PhysicalSourceInputJoin.edgeArrayCode source
      ∃ post rounds : Code,
        (match (PhysicalSourceInputJoin.edge source).1 with
        | none => post=[]
        | some ⟨_,D⟩ => FramedEdgeStorage.AfterInput D input post) ∧
        FramedEdgePackedLayout.ModelWith RunnerProjectionLayout.Model κ mode source tape rounds ∧
        let data := input++post++rounds++FramedEdgeTerminalArrays.wireCode κ mode source tape
        let frames := FramedSolverStackLayout.edge κ mode source tape
        solver.1.2+solver.2.1.total+solver.2.2+reservationWork heap data+reservationWork stack frames ≤
          p.eval (source.length+κ+heap.size+stack.size) := by
  obtain ⟨base,recorded⟩ := FramedProjectedRoundWork.edge
  obtain ⟨cells,steps,stacked⟩ := FramedSolverStackLayout.edge_polynomial
  refine ⟨base+budget 0 cells steps,?_⟩
  intro κ heap stack mode source tape
  obtain ⟨post,rounds,prefixModel,roundModel,work⟩ := recorded κ heap mode source tape
  obtain ⟨frameSpace,frameSteps⟩ := stacked κ mode source tape
  have frames := reservations_le cells steps (source.length+κ) stack
    (FramedSolverStackLayout.edge κ mode source tape) frameSpace frameSteps
  let x := source.length+κ+heap.size+stack.size
  have heapWidth : source.length+κ+heap.size ≤ x := Nat.le_add_right _ _
  have stackWidth : source.length+κ+stack.size ≤ x := by dsimp only [x]; omega
  refine ⟨post,rounds,prefixModel,roundModel,?_⟩
  simp only [PaidDirectEdgeWire.edge_terminal_frame_stack_reference,eval_add]
  exact Nat.add_le_add (work.trans (eval_mono _ heapWidth)) (frames.trans (eval_mono _ stackWidth))

end DirectedFlowCutGap.FramedStackReservationWork
