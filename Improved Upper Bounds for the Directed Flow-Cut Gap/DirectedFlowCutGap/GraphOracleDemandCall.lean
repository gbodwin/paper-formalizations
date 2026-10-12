import DirectedFlowCutGap.GraphOracleProgram

namespace DirectedFlowCutGap.GraphOracleMachine
open BinaryArithmetic BinaryRational BinaryFractionalRows IntegralNetworkFlow IntegralNetworkFlow.Tabulated
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor

theorem demand_return {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (y : Row n) (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    {xs : List DemandCollection.Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (DemandCollection.EncodesDemand label) xs ds)
    {heap : NaturalHeap} {a b : ℕ} (input : DemandCollection.DemandList heap a xs)
    (shared : DemandCollection.Shared heap b ((ResidualSearch.Enumeration.fin n).vertices.map label)
      (GraphRelaxationRefinement.matrix adjacency) y.toList)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 2120)
    (stack : List (Frame ℕ 2120)) (source : Bits) :
    ∃ ext root,ext.length=DemandCollection.selectedCells ((ResidualSearch.Enumeration.fin n).vertices.map label)
        (GraphRelaxationRefinement.matrix adjacency) y.toList next xs ∧
      NaturalRun program (DemandCollection.selectedSteps ((ResidualSearch.Enumeration.fin n).vertices.map label)
        (GraphRelaxationRefinement.matrix adjacency) y.toList next xs+1)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 1600) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      DemandCollection.SelectedOrigin (heap++ext) root label (BinaryFractionalGraphOracle.selected adjacency y ds).1 ∧
      DemandCollection.DemandList (heap++ext) a xs := by
  obtain ⟨out,high,selected,retained,src,stk,dense,⟨ext,he,len⟩,halt⟩ :=
    DemandCollection.graph_origin_high adjacency y label hlabel encoded
      (DemandCollection.state heap next a b c d [] source 1600) rfl hn rfl input shared
  let frames := (⟨pc,.r3,saved⟩::stack)
  have mapped := ReferenceProgramLabels.run demandLabel DemandCollection.program program demand_slots high
  have lifted := ReferenceProgramStack.run program frames mapped
  have finish : tickNatural program (ReferenceProgramStack.state frames (ReferenceProgramLabels.state demandLabel out))=
      some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c out.registers.d stack source pc,[],0⟩ := by
    simp [tickNatural,ReferenceProgramStack.state,ReferenceProgramLabels.state,demand_halt out.pc halt,
      frames,stk,src,DemandCollection.state,state,Registers.get,Registers.set,dense,he,hn]
  refine ⟨ext,out.registers.d,len,?_,?_,?_⟩
  · simpa [ReferenceProgramStack.state,ReferenceProgramLabels.state,DemandCollection.state,demandLabel,state] using
      run_append lifted (.step finish (.done _))
  · simpa [he,DemandCollection.state] using selected
  · simpa [he,DemandCollection.state] using retained

end DirectedFlowCutGap.GraphOracleMachine
