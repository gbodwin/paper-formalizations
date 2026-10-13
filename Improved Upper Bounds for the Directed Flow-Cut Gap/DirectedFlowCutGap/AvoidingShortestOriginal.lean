import DirectedFlowCutGap.AvoidingShortestRefinement
import DirectedFlowCutGap.BinaryWalkCostCongruence

namespace DirectedFlowCutGap.AvoidingShortest
open BinaryArithmetic BinaryRational BinaryFractionalRows IntegralNetworkFlow IntegralNetworkFlow.Tabulated

theorem zero_outgoing {n : ℕ} (s : Fin n) (e : BinaryFractionalWalkOracle.Pair n) :
    (BinaryFractionalGraphOracle.outgoing (zeroRow n) s e).1=BinaryRational.zero := by
  unfold BinaryFractionalGraphOracle.outgoing
  split
  · rfl
  · simp [BinaryFractionalGraphOracle.read_value,BinaryFractionalRows.get,zeroRow]

theorem result_constant {n : ℕ} (E : ResidualSearch.Enumeration (Fin n))
    (adjacency : BinaryFractionalWalkOracle.Adjacency n) (s t : Fin n)
    (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val) :
    result (E.vertices.map label) (GraphRelaxationRefinement.matrix adjacency) (label s) (label t)=
      (BinaryFractionalWalkOracle.shortest E adjacency (fun _ => (BinaryRational.zero,1)) s t).1.map
        (GraphRelaxationRefinement.encode label) := by
  rw [result_original E adjacency s t label hlabel,
    BinaryFractionalWalkOracle.shortest_cost_eq (BinaryFractionalGraphOracle.outgoing (zeroRow n) s)
      (fun _ => (BinaryRational.zero,1)) (zero_outgoing s)]
end DirectedFlowCutGap.AvoidingShortest
