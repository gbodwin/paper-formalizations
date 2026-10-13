import DirectedFlowCutGap.AvoidingKeptPathCallLift

namespace DirectedFlowCutGap.AvoidingKeptPath
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor
open IntegralNetworkFlow IntegralNetworkFlow.Tabulated

theorem enum_map (n : ℕ) (label : Fin n → Bits) :
    (ResidualSearch.Enumeration.fin n).vertices.map label=List.ofFn label := by
  simp [ResidualSearch.Enumeration.fin,ResidualSearch.Enumeration.ofEquiv,List.map_ofFn]

theorem matrix_return {heap : NaturalHeap} {a b : ℕ} {s t : Bits} {vs : List Bits}
    {costs : List (Bits × Bits)} {rows : List Bits}
    (hv : GraphDiscoveryProgram.Vertices heap a vs) (hc : KeptAdjacencyInput.Context heap b s t costs rows)
    (aligned : vs.length=costs.length) (height : rows.length=vs.length)
    (widths : ∀ u∈rows,u.length=vs.length)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 1800)
    (stack : List (Frame ℕ 1800)) (source : Bits) :
    ∃ ext root,ext.length=KeptAdjacencyInput.cells s t vs costs rows ∧
      NaturalRun program (KeptAdjacencyInput.steps s t vs costs rows+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 318) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      KeptAdjacencyInput.Matrix (heap++ext) root (KeptAdjacencyInput.result s t vs costs rows) := by
  obtain ⟨ext,root,len,run,rep⟩ := KeptAdjacencyInput.scan hv hc aligned height widths next c d hn [] source
  have lifted := child_return matrixLabel KeptAdjacencyInput.program matrix_slots run rfl rfl
    .r3 .r3 saved pc stack (by rfl)
  refine ⟨ext,root,len,?_,rep⟩
  simpa [KeptAdjacencyInput.state,matrixLabel,state,Registers.get,Registers.set,Nat.add_assoc] using lifted

theorem shortest_return {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n) (s t : Fin n)
    (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    {heap : NaturalHeap} {a b : ℕ}
    (input : GraphDiscoveryProgram.Vertices heap a (List.ofFn label))
    (metadata : AvoidingZeroContext.Static heap b (GraphRelaxationRefinement.matrix adjacency) (label s) (label t))
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 1800)
    (stack : List (Frame ℕ 1800)) (source : Bits) :
    ∃ ext root,ext.length=AvoidingShortest.cells (List.ofFn label) (GraphRelaxationRefinement.matrix adjacency) (label s) (label t) ∧
      NaturalRun program (AvoidingShortest.steps (List.ofFn label) (GraphRelaxationRefinement.matrix adjacency) (label s) (label t)+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 1758) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      GraphDiscoveryProgram.StoredOption (heap++ext) root
        (AvoidingShortest.result (List.ofFn label) (GraphRelaxationRefinement.matrix adjacency) (label s) (label t)) := by
  obtain ⟨ext,root,len,run,rep⟩ := AvoidingShortest.search (ResidualSearch.Enumeration.fin n) adjacency s t label hlabel
    (by simpa only [enum_map] using input) metadata next c d hn [] source
  have lifted := child_return shortestLabel AvoidingShortest.program shortest_slots run rfl rfl
    .r3 .r3 saved pc stack (by rfl)
  refine ⟨ext,root,by simpa only [enum_map] using len,?_,?_⟩
  · simpa [AvoidingShortest.state,shortestLabel,state,Registers.get,Registers.set,Nat.add_assoc,enum_map] using lifted
  · simpa only [←AvoidingShortest.result_constant (ResidualSearch.Enumeration.fin n) adjacency s t label hlabel,enum_map] using rep
end DirectedFlowCutGap.AvoidingKeptPath
