import DirectedFlowCutGap.DemandSelectionOrigin

namespace DirectedFlowCutGap.DemandCollection
open BinaryArithmetic BinaryRational BinaryFractionalRows IntegralNetworkFlow IntegralNetworkFlow.Tabulated
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor

theorem graph_origin_high {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (y : Row n) (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    {xs : List Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (EncodesDemand label) xs ds) (initial : NaturalState 1604)
    (pc0 : initial.pc=1600) (hn : initial.next=initial.heap.length) (empty : initial.stack=[])
    (input : DemandList initial.heap initial.registers.a xs)
    (shared : Shared initial.heap initial.registers.b ((ResidualSearch.Enumeration.fin n).vertices.map label)
      (GraphRelaxationRefinement.matrix adjacency) y.toList) :
    ∃ out,NaturalRun program (selectedSteps ((ResidualSearch.Enumeration.fin n).vertices.map label)
        (GraphRelaxationRefinement.matrix adjacency) y.toList initial.next xs) initial [] out ∧
      SelectedOrigin out.heap out.registers.d label (BinaryFractionalGraphOracle.selected adjacency y ds).1 ∧
      DemandList out.heap initial.registers.a xs ∧ out.source=initial.source ∧ out.stack=[] ∧
      out.next=out.heap.length ∧
      (∃ ext,out.heap=initial.heap++ext ∧ ext.length=selectedCells ((ResidualSearch.Enumeration.fin n).vertices.map label)
        (GraphRelaxationRefinement.matrix adjacency) y.toList initial.next xs) ∧ program out.pc=.halt := by
  have rows : n≤(GraphRelaxationRefinement.matrix adjacency).length := by simp [GraphRelaxationRefinement.matrix_length]
  have cols : ∀ (i : ℕ) (hi : i<n),n≤((GraphRelaxationRefinement.matrix adjacency)[i]'(lt_of_lt_of_le hi rows)).length :=
    fun i hi => (GraphRelaxationRefinement.matrix_row_length adjacency ⟨i,hi⟩).ge
  have hv : ∀ v∈(ResidualSearch.Enumeration.fin n).vertices.map label,value v<n := by
    intro v hv
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hv
    rw [hlabel]
    exact i.isLt
  have hc : ∀ v∈(ResidualSearch.Enumeration.fin n).vertices.map label,value v<y.toList.length := by
    simpa only [Vector.length_toList] using hv
  obtain ⟨out,run,selected,⟨root,records⟩,retained,source,stack,dense,ext,halt⟩ :=
    selected_high n initial pc0 hn empty input shared rows cols hv hc
      (encoded_query_valid adjacency y label hlabel encoded)
  refine ⟨out,run,?_,retained,source,stack,dense,ext,halt⟩
  exact selected_origin label records retained (records_original _ _ _ _ _) selected (selected_records_refine adjacency y label hlabel encoded initial.next)

end DirectedFlowCutGap.DemandCollection
