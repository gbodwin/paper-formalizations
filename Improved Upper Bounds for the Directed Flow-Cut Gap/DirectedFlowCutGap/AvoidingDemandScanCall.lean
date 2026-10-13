import DirectedFlowCutGap.AvoidingDemandScanCallLift

namespace DirectedFlowCutGap.AvoidingDemandScan
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor
open IntegralNetworkFlow IntegralNetworkFlow.Tabulated

theorem query_return {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n) (s t : Fin n)
    (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    {heap : NaturalHeap} {a b : ℕ}
    (input : GraphDiscoveryProgram.Vertices heap a (List.ofFn label))
    (metadata : KeptAdjacencyInput.Context heap b (label s) (label t)
      (IndexedRationalRead.fields costs.toList) (GraphRelaxationRefinement.matrix adjacency))
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 1900)
    (stack : List (Frame ℕ 1900)) (source : Bits) :
    ∃ ext root,ext.length=AvoidingKeptPath.cells (label s) (label t) (List.ofFn label)
      (IndexedRationalRead.fields costs.toList) (GraphRelaxationRefinement.matrix adjacency) ∧
      NaturalRun program (AvoidingKeptPath.steps (label s) (label t) (List.ofFn label)
        (IndexedRationalRead.fields costs.toList) (GraphRelaxationRefinement.matrix adjacency)+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 1798) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      GraphDiscoveryProgram.StoredOption (heap++ext) root
        (AvoidingKeptPath.result (label s) (label t) (List.ofFn label)
          (IndexedRationalRead.fields costs.toList) (GraphRelaxationRefinement.matrix adjacency)) := by
  obtain ⟨ext,root,len,run,rep⟩ := AvoidingKeptPath.search adjacency costs s t label hlabel input metadata
    next c d hn [] source
  have lifted := child_return queryLabel AvoidingKeptPath.program query_slots run rfl rfl
    .r3 .r3 saved pc stack (by rfl)
  refine ⟨ext,root,len,?_,?_⟩
  · simpa [AvoidingKeptPath.state,queryLabel,state,Registers.get,Registers.set,Nat.add_assoc] using lifted
  · simpa only [←AvoidingKeptPath.result_original adjacency costs s t label hlabel] using rep
end DirectedFlowCutGap.AvoidingDemandScan
