import DirectedFlowCutGap.GraphOracleExecution
import DirectedFlowCutGap.DemandCollectionBounds
import DirectedFlowCutGap.BinaryFractionalGraphBounds

namespace DirectedFlowCutGap.GraphOracleMachine
open BinaryArithmetic BinaryRational BinaryFractionalRows

def instructionBound (demands n W : ℕ) : ℕ :=
  DemandCollection.instructionBound demands n W+OracleMask.instructionBound n n W+
    CapacityBottleneck.instructionBound n W+6*n+40

theorem selected_path_bound {n W : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (y : Row n) (ds : List (BinaryFractionalWalkOracle.Pair n))
    (widths : ∀ q∈y.toList,StoredBounded q W) :
    (((BinaryFractionalGraphOracle.selected adjacency y ds).1.map fun q => q.path.edges.length).getD 0)≤n := by
  have hy : ∀ i,StoredBounded (get y i) W := by
    intro i
    apply widths
    simp [BinaryFractionalRows.get]
  have property := BinaryFractionalGraphBounds.selected_properties adjacency y hy ds
  cases hq : (BinaryFractionalGraphOracle.selected adjacency y ds).1 with
  | none => simp
  | some q =>
    have h := (property q hq).2
    simpa using h

theorem post_steps_bound {n W : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (y : Row n) (ds : List (BinaryFractionalWalkOracle.Pair n))
    (widths : ∀ q∈y.toList,StoredBounded q W) :
    OracleChoice.instructionBound (BinaryFractionalGraphOracle.selected adjacency y ds).1 W≤
      OracleMask.instructionBound n n W+CapacityBottleneck.instructionBound n W+6*n+30 := by
  have length := selected_path_bound adjacency y ds widths
  unfold OracleChoice.instructionBound OracleMask.instructionBound
  gcongr

end DirectedFlowCutGap.GraphOracleMachine
