import DirectedFlowCutGap.BinaryFractionalGraphBounds
import DirectedFlowCutGap.BinaryFractionalEntryCost

/-!
# Covering recurrence with the actual graph oracle cost substituted

This component removes the generic oracle charge premise from the covering
entry bound. The concrete graph program supplies every oracle choice and its
computed charge, and the retained state invariant supplies all operand widths.
The expression is a polynomial in vertex count, demand-list length and maximum
supplied fraction length. A fixed-body representation simulation is the separate
step that turns these instrumented charges into a full machine-cost theorem.
-/
namespace DirectedFlowCutGap.BinaryFractionalGraphCost
open BinaryRational BinaryFractionalRows BinaryFractionalWalkOracle
open BinaryFractionalGraphOracle BinaryFractionalGraphBounds BinaryFractionalWidths
variable {n B : ℕ}

def solveGraphBound (n D B : ℕ) : ℕ :=
  BinaryFractionalEntryCost.entryBound n B
    (oracleBound n D B (stateWidth n B (3*n^2)))

/-- The oracle is the implemented graph oracle, with no external runtime premise. -/
theorem solveGraph_charge (adjacency : Adjacency n) (ds : List (Pair n))
    (c : Row n) (hn : 0<n) (hc : RowStored c B) :
    (solveGraph adjacency ds c hn).operations ≤ solveGraphBound n ds.length B := by
  exact BinaryFractionalEntryCost.solveInput_charge c (oracle adjacency ds c hn)
    (FractionalCoverRawGraph.oracle (graph adjacency) ds (BinaryFractionalRows.decodeRow c) hn)
    (oracle_refines adjacency ds c hn) B _ hc
    (fun y hy => oracle_charge adjacency ds c y hn hc hy)

/-- Full raw-state refinement and the concrete polynomial charge describe the
same run, including its fixed number of stopping tests. -/
theorem solveGraph_refines_and_charge (adjacency : Adjacency n) (ds : List (Pair n))
    (c : Row n) (hn : 0<n) (hc : RowStored c B) :
    BinaryFractionalCore.decodeState (solveGraph adjacency ds c hn).state =
      FractionalCoverRawGraph.solveGraph (graph adjacency) ds (BinaryFractionalRows.decodeRow c) hn ∧
    (solveGraph adjacency ds c hn).stopTests=3*n^2 ∧
    (solveGraph adjacency ds c hn).operations ≤ solveGraphBound n ds.length B := by
  have h := solveGraph_refines adjacency ds c hn
  exact ⟨h.1,h.2,solveGraph_charge adjacency ds c hn hc⟩

end DirectedFlowCutGap.BinaryFractionalGraphCost
