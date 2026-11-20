import DirectedFlowCutGap.FramedChargedReservations
import DirectedFlowCutGap.RunnerProjectionLayout

/-! Join the reached inner mask pullbacks after preparation and cutoff,
including the vertex runner invoked inside each attempted edge round. -/
namespace DirectedFlowCutGap.FramedProjectedRoundWork

open BinaryArithmetic Polynomial
open BinaryArrayNestedStorage (Code)

theorem vertex : ∃ p : Polynomial ℕ,
    ∀ (κ start : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits),
      let solver := PaidFramedVertexWire.vertexWithTerminalRowWork κ mode source tape
      ∃ post rounds : Code, FramedVertexPackedLayout.Prefix source post ∧
        FramedVertexPackedLayout.ModelWith RunnerProjectionLayout.Model κ mode source tape rounds ∧
        let trace := PhysicalSourceInputJoin.vertexArrayCode source++post++rounds
        solver.1.2+solver.2.1+solver.2.2+FramedChargedReservations.reservationWork start trace ≤ p.eval (source.length+κ+start.size) :=
  FramedChargedReservations.vertexWith RunnerProjectionLayout.Model RunnerProjectionLayout.arrays

theorem edge : ∃ p : Polynomial ℕ,
    ∀ (κ start : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits),
      let solver := PaidDirectEdgeWire.edgeWithTerminalRowWork κ mode source tape
      let input := PhysicalSourceInputJoin.edgeArrayCode source
      ∃ post rounds : Code,
        (match (PhysicalSourceInputJoin.edge source).1 with
        | none => post=[]
        | some ⟨_,D⟩ => FramedEdgeStorage.AfterInput D input post) ∧
        FramedEdgePackedLayout.ModelWith RunnerProjectionLayout.Model κ mode source tape rounds ∧
        let trace := input++post++rounds++FramedEdgeTerminalArrays.wireCode κ mode source tape
        solver.1.2+solver.2.1.total+solver.2.2+FramedChargedReservations.reservationWork start trace ≤ p.eval (source.length+κ+start.size) :=
  FramedChargedReservations.edgeWith RunnerProjectionLayout.Model RunnerProjectionLayout.arrays

end DirectedFlowCutGap.FramedProjectedRoundWork
