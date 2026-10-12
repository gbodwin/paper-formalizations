import DirectedFlowCutGap.ActualDemandSelection
import DirectedFlowCutGap.DemandCollectionBounds

/-! The same actual collection-and-selection run has a bound in the original
number of demands, graph order and represented word width, including its halt. -/
namespace DirectedFlowCutGap.DemandCollection
open BinaryArithmetic BinaryRational BinaryFractionalRows IntegralNetworkFlow IntegralNetworkFlow.Tabulated
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor

theorem graph_bit_bounded {n H A : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (y : Row n) (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    {xs : List Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (EncodesDemand label) xs ds) (initial : BitState 1604)
    (bounded : initial.Bounded H A) (pc0 : initial.pc=1600)
    (hn : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (input : DemandList (eraseState initial).heap (eraseState initial).registers.a xs)
    (shared : Shared (eraseState initial).heap (eraseState initial).registers.b
      ((ResidualSearch.Enumeration.fin n).vertices.map label) (GraphRelaxationRefinement.matrix adjacency) y.toList)
    (W : ℕ) (hW : 1 ≤ W) (labels : ∀ i,(label i).length ≤ W)
    (rowWidths : ∀ q∈y.toList,StoredBounded q W) :
    ∃ charge out,Run program (selectedSteps ((ResidualSearch.Enumeration.fin n).vertices.map label)
        (GraphRelaxationRefinement.matrix adjacency) y.toList (value initial.next) xs) charge initial [] out ∧
      GraphSelected (eraseState out).heap (eraseState out).registers.d label (BinaryFractionalGraphOracle.selected adjacency y ds).1 ∧
      DemandList (eraseState out).heap (eraseState initial).registers.a xs ∧
      out.source=initial.source ∧ out.stack=[] ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext ∧
        ext.length=selectedCells ((ResidualSearch.Enumeration.fin n).vertices.map label)
          (GraphRelaxationRefinement.matrix adjacency) y.toList (value initial.next) xs) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations≤completeBound 1604 H A (instructionBound xs.length n W) := by
  obtain ⟨charge,out,run,result,retained,source,stack,ext,halt,price⟩ :=
    graph_bit adjacency y label hlabel encoded initial bounded pc0 hn empty input shared
  have bound := graph_steps_bound adjacency y label hlabel encoded (value initial.next) W hW labels rowWidths
  exact ⟨charge,out,run,result,retained,source,stack,ext,halt,
    price.trans (SupportSearchEncoding.complete_mono 1604 H A _ _ bound)⟩

end DirectedFlowCutGap.DemandCollection
