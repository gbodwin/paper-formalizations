import DirectedFlowCutGap.GraphDiscoveryExecution
import DirectedFlowCutGap.GraphDiscoveryRefinement

/-! An actual fixed instruction program constructs all bounded relaxation
tables and returns the literal frozen graph minimizer. No prior relaxation
table, output candidate, adjacency callback or computed path cost is supplied.
The graph/row/enumeration input representations and later support-search recovery
remain explicit boundaries. -/
namespace DirectedFlowCutGap.ActualGraphDiscovery
open BinaryArithmetic BinaryRational BinaryFractionalRows GraphWalkExtension
open GraphRelaxationRefinement GraphDiscoveryProgram IntegralNetworkFlow

theorem graph_bit {n H A : ℕ} (E : ResidualSearch.Enumeration (Fin n))
    (adjacency : BinaryFractionalWalkOracle.Adjacency n) (y : Row n) (s t : Fin n)
    (sw : Bits) (hs : value sw=s.val) (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (initial : ImmutableReferenceSimulation.BitState 720) (bounded : initial.Bounded H A)
    (pc0 : initial.pc=717) (hn : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (input : Vertices (ImmutableReferenceSimulation.eraseState initial).heap
      (ImmutableReferenceSimulation.eraseState initial).registers.a (E.vertices.map label))
    (context : GlobalContext (ImmutableReferenceSimulation.eraseState initial).heap
      (ImmutableReferenceSimulation.eraseState initial).registers.b (E.vertices.map label)
      (matrix adjacency) y.toList sw (label t))
    (word : BooleanTableRead.BoolList (ImmutableReferenceSimulation.eraseState initial).heap
      (ImmutableReferenceSimulation.eraseState initial).registers.c (label s))
    (B : ℕ) (hB : 1 ≤ B) (hr : ∀ q∈y.toList,StoredBounded q B) (labels : ∀ i,(label i).length ≤ B) :
    ∃ charge out,ImmutableReferenceSimulation.Run GraphDiscoveryProgram.program
      (minimizeSteps (E.vertices.map label) (matrix adjacency) y.toList sw (label t) (label s)+1)
      charge initial [] out ∧
      StoredOption (ImmutableReferenceSimulation.eraseState out).heap
        (ImmutableReferenceSimulation.eraseState out).registers.d
        ((BinaryFractionalWalkOracle.minimize E adjacency (BinaryFractionalGraphOracle.outgoing y s) s t).1.map (encode label)) ∧
      Vertices (ImmutableReferenceSimulation.eraseState out).heap
        (ImmutableReferenceSimulation.eraseState initial).registers.a (E.vertices.map label) ∧
      GlobalContext (ImmutableReferenceSimulation.eraseState out).heap
        (ImmutableReferenceSimulation.eraseState initial).registers.b (E.vertices.map label)
        (matrix adjacency) y.toList sw (label t) ∧
      BooleanTableRead.BoolList (ImmutableReferenceSimulation.eraseState out).heap
        (ImmutableReferenceSimulation.eraseState initial).registers.c (label s) ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=719 ∧
      (∃ ext,(ImmutableReferenceSimulation.eraseState out).heap=(ImmutableReferenceSimulation.eraseState initial).heap++ext ∧
        ext.length=minimizeCells (E.vertices.map label) (matrix adjacency) y.toList sw (label t) (label s)) ∧
      (ImmutableReferenceTerminal.attempt GraphDiscoveryProgram.program out).result=none ∧
      charge+(ImmutableReferenceTerminal.attempt GraphDiscoveryProgram.program out).operations ≤
        ImmutableReferenceTerminal.completeBound 720 H A (discoveryBudget E.vertices.length B n sw.length) := by
  have hi : ∀ u∈E.vertices.map label,value u<(matrix adjacency).length := by
    intro u hu
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hu
    simp [hlabel,matrix]
  have hc : ∀ u∈E.vertices.map label,value u<y.toList.length := by
    intro u hu
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hu
    simp [hlabel]
  have targetCol : ∀ v,(hv : v∈E.vertices.map label) → value (label t)<((matrix adjacency)[value v]'(hi v hv)).length := by
    intro v hv
    obtain ⟨z,_,rfl⟩ := List.mem_map.mp hv
    simp [hlabel,matrix]
  have columns : ∀ v,(hv : v∈E.vertices.map label) → ∀ z∈E.vertices.map label,
      value z<((matrix adjacency)[value v]'(hi v hv)).length := by
    intro v hv z hz
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hv
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hz
    simp [hlabel,matrix]
  have hv : ∀ v∈E.vertices.map label,v.length ≤ B ∧ value v ≤ n := by
    intro v hv
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hv
    exact ⟨labels i,by simp [hlabel]⟩
  have result := minimize_bit initial bounded pc0 hn empty input context word hi hc targetCol columns
    B n hB hr (labels t) (by simp [hlabel]) (labels s) hv
  simp only [minimize,GraphDiscoveryRefinement.minimize_eq E adjacency y s t sw hs label hlabel,
    List.length_map] at result
  exact result

end DirectedFlowCutGap.ActualGraphDiscovery
