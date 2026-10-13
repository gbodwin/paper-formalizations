import DirectedFlowCutGap.AvoidingShortestBounds
import DirectedFlowCutGap.AvoidingShortestOriginal

namespace DirectedFlowCutGap.AvoidingShortest
open BinaryArithmetic BinaryRational IntegralNetworkFlow IntegralNetworkFlow.Tabulated
open ImmutableReferenceSimulation BooleanTableRead

theorem search {n : ℕ} (E : ResidualSearch.Enumeration (Fin n))
    (adjacency : BinaryFractionalWalkOracle.Adjacency n) (s t : Fin n)
    (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    {heap : NaturalHeap} {a b : ℕ}
    (input : GraphDiscoveryProgram.Vertices heap a (E.vertices.map label))
    (metadata : AvoidingZeroContext.Static heap b (GraphRelaxationRefinement.matrix adjacency) (label s) (label t))
    (next c d : ℕ) (hn : next=heap.length) (stack : List (Frame ℕ 1440)) (source : Bits) :
    ∃ ext root,ext.length=cells (E.vertices.map label) (GraphRelaxationRefinement.matrix adjacency) (label s) (label t) ∧
      NaturalRun program (steps (E.vertices.map label) (GraphRelaxationRefinement.matrix adjacency) (label s) (label t)+1)
        (state heap next a b c d stack source 1438) []
        (state (heap++ext) (next+ext.length) a b c root stack source 1439) ∧
      GraphDiscoveryProgram.StoredOption (heap++ext) root
        ((BinaryFractionalWalkOracle.shortest E adjacency (fun _ => (BinaryRational.zero,1)) s t).1.map
          (GraphRelaxationRefinement.encode label)) := by
  obtain ⟨ext,root,len,run,rep⟩ := typed_return E adjacency s t label hlabel input metadata next c d hn
    ⟨a,b,c,d⟩ 1439 stack source
  have call : tickNatural program (state heap next a b c d stack source 1438)=
      some ⟨state heap next a b c d (⟨1439,.r3,⟨a,b,c,d⟩⟩::stack) source 1410,[],0⟩ := rfl
  refine ⟨ext,root,len,.step call run,?_⟩
  simpa only [BinaryFractionalWalkOracle.shortest_cost_eq
    (BinaryFractionalGraphOracle.outgoing (zeroRow n) s) (fun _ => (BinaryRational.zero,1)) (zero_outgoing s)] using rep
end DirectedFlowCutGap.AvoidingShortest
