import DirectedFlowCutGap.GraphRecoveryController
import DirectedFlowCutGap.GraphDiscoveryRefinement
import DirectedFlowCutGap.CostedSupportRefinement

namespace DirectedFlowCutGap.GraphRecoveryController
open BinaryArithmetic BinaryRational BinaryFractionalRows IntegralNetworkFlow IntegralNetworkFlow.Tabulated
open SupportSearchEncoding GraphWalkExtension

theorem result_eq {n : ℕ} (E : ResidualSearch.Enumeration (Fin n))
    (adjacency : BinaryFractionalWalkOracle.Adjacency n) (y : Row n) (s t : Fin n)
    (sw : Bits) (hs : value sw=s.val) (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val) :
    result (E.vertices.map label) (GraphRelaxationRefinement.matrix adjacency) y.toList sw (label t) (label s)=
      (BinaryFractionalWalkOracle.shortest E adjacency (BinaryFractionalGraphOracle.outgoing y s) s t).1.map
        (GraphRelaxationRefinement.encode label) := by
  have hm := GraphDiscoveryRefinement.minimize_eq E adjacency y s t sw hs label hlabel
  change GraphDiscoveryProgram.minimize _ _ _ _ _ _=_ at hm
  unfold result
  rw [hm]
  unfold BinaryFractionalWalkOracle.shortest
  dsimp only
  cases hq : (BinaryFractionalWalkOracle.minimize E adjacency (BinaryFractionalGraphOracle.outgoing y s) s t).1 with
  | none => simp only [Option.map_none]
  | some q =>
    simp only [Option.map_some]
    have he := congrArg some (CostedSupportProgram.result_eq E adjacency q.edges y s t sw hs label hlabel)
    have ef : SupportSearchEncoding.encodeEdge label=(fun e => (label e.1,label e.2)) := rfl
    rw [ef] at he
    simpa only [GraphRelaxationRefinement.encode] using he

theorem recovery_valid {n : ℕ} (E : ResidualSearch.Enumeration (Fin n))
    (adjacency : BinaryFractionalWalkOracle.Adjacency n) (y : Row n) (s t : Fin n)
    (sw : Bits) (hs : value sw=s.val) (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (q : Walk) (chosen : GraphDiscoveryProgram.minimize (E.vertices.map label)
      (GraphRelaxationRefinement.matrix adjacency) y.toList sw (label t) (label s)=some q) :
    ∀ w∈(CostedSupportProgram.edges (E.vertices.map label) (GraphRelaxationRefinement.matrix adjacency)
      q.edges sw (label t)).map Prod.fst,value w<y.toList.length := by
  have hm := GraphDiscoveryRefinement.minimize_eq E adjacency y s t sw hs label hlabel
  change GraphDiscoveryProgram.minimize _ _ _ _ _ _=_ at hm
  rw [chosen] at hm
  cases hq : (BinaryFractionalWalkOracle.minimize E adjacency (BinaryFractionalGraphOracle.outgoing y s) s t).1 with
  | none => simp [hq] at hm
  | some old =>
    simp only [hq,Option.map_some,Option.some.injEq] at hm
    subst q
    have hv := MaterializedGraphPath.indices_valid
      (CostedSupportProgram.recovered_encoding E adjacency old.edges s t sw hs label hlabel)
    have ef : SupportSearchEncoding.encodeEdge label=(fun e => (label e.1,label e.2)) := rfl
    rw [ef] at hv
    simpa only [Vector.length_toList,GraphRelaxationRefinement.encode] using hv

end DirectedFlowCutGap.GraphRecoveryController
