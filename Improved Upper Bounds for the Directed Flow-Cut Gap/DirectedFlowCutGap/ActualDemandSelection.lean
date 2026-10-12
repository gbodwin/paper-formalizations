import DirectedFlowCutGap.DemandCollectionSelection
import DirectedFlowCutGap.DemandSelectedPayload

/-! Actual demand traversal, discovered/recovered path records and stable graph
selection share one lower-machine run. The input contains only graph data and
original demand pairs; every selected path and cost is constructed by code. -/
namespace DirectedFlowCutGap.DemandCollection
open BinaryArithmetic BinaryRational BinaryFractionalRows IntegralNetworkFlow IntegralNetworkFlow.Tabulated
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor

theorem graph_high {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (y : Row n) (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    {xs : List Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (EncodesDemand label) xs ds) (initial : NaturalState 1604)
    (pc0 : initial.pc=1600) (hn : initial.next=initial.heap.length) (empty : initial.stack=[])
    (input : DemandList initial.heap initial.registers.a xs)
    (shared : Shared initial.heap initial.registers.b ((ResidualSearch.Enumeration.fin n).vertices.map label)
      (GraphRelaxationRefinement.matrix adjacency) y.toList) :
    ∃ out,NaturalRun program (selectedSteps ((ResidualSearch.Enumeration.fin n).vertices.map label)
        (GraphRelaxationRefinement.matrix adjacency) y.toList initial.next xs) initial [] out ∧
      GraphSelected out.heap out.registers.d label (BinaryFractionalGraphOracle.selected adjacency y ds).1 ∧
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
  exact selected_payload label records selected (selected_records_refine adjacency y label hlabel encoded initial.next)

theorem graph_bit {n H A : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (y : Row n) (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    {xs : List Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (EncodesDemand label) xs ds) (initial : BitState 1604)
    (bounded : initial.Bounded H A) (pc0 : initial.pc=1600)
    (hn : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (input : DemandList (eraseState initial).heap (eraseState initial).registers.a xs)
    (shared : Shared (eraseState initial).heap (eraseState initial).registers.b
      ((ResidualSearch.Enumeration.fin n).vertices.map label) (GraphRelaxationRefinement.matrix adjacency) y.toList) :
    ∃ charge out,Run program (selectedSteps ((ResidualSearch.Enumeration.fin n).vertices.map label)
        (GraphRelaxationRefinement.matrix adjacency) y.toList (value initial.next) xs) charge initial [] out ∧
      GraphSelected (eraseState out).heap (eraseState out).registers.d label (BinaryFractionalGraphOracle.selected adjacency y ds).1 ∧
      DemandList (eraseState out).heap (eraseState initial).registers.a xs ∧
      out.source=initial.source ∧ out.stack=[] ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext ∧
        ext.length=selectedCells ((ResidualSearch.Enumeration.fin n).vertices.map label)
          (GraphRelaxationRefinement.matrix adjacency) y.toList (value initial.next) xs) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations≤completeBound 1604 H A
        (selectedSteps ((ResidualSearch.Enumeration.fin n).vertices.map label)
          (GraphRelaxationRefinement.matrix adjacency) y.toList (value initial.next) xs) := by
  have hn' : (eraseState initial).next=(eraseState initial).heap.length := by simpa [eraseState,State.map] using hn
  have empty' : (eraseState initial).stack=[] := by simp [eraseState,State.map,empty]
  obtain ⟨final,high,selected,retained,source,stack,_,ext,halt⟩ :=
    graph_high adjacency y label hlabel encoded (eraseState initial) pc0 hn' empty' input shared
  obtain ⟨charge,out,run,erase,_,_,src⟩ := polynomial_simulation bounded high
  have stop : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase] at obs
    have ht : tickNatural program final=none := by simp [tickNatural,halt]
    rw [ht] at obs
    cases h : tick program out with
    | none => rfl
    | some r => simp [h] at obs
  refine ⟨charge,out,run,?_,?_,src.trans source,?_,?_,stop,(terminal_accounting run bounded stop).2⟩
  · rw [erase];exact selected
  · rw [erase];exact retained
  · have h : (eraseState out).stack=[] := by rw [erase];exact stack
    simpa [eraseState,State.map] using h
  · rw [erase];exact ext

end DirectedFlowCutGap.DemandCollection
