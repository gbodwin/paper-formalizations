import DirectedFlowCutGap.CostedSupportExecution
import DirectedFlowCutGap.CostedSupportRefinement

/-! Actual support traversal and canonical path-cost computation in one lower
run. The input supplies graph data and the support edge list, not a recovered
path, its cost list, or its final cost. Discovery and outer control remain later joins. -/
namespace DirectedFlowCutGap.CostedSupportProgram
open BinaryArithmetic BinaryRational BinaryFractionalRows IntegralNetworkFlow IntegralNetworkFlow.Tabulated
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead GraphWalkExtension
open SupportSearchEncoding PackedBooleanConstructor

theorem graph_bit {n H A : ℕ} (E : ResidualSearch.Enumeration (Fin n))
    (adjacency : BinaryFractionalWalkOracle.Adjacency n) (es : List (Fin n×Fin n)) (y : Row n) (s t : Fin n)
    (sw : Bits) (hsw : value sw=s.val) (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (initial : BitState 592) (bounded : initial.Bounded H A)
    (pc0 : initial.pc=590) (hn : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (input : SupportRecoveryProgram.Vertices (eraseState initial).heap (eraseState initial).registers.a
      (E.vertices.map label))
    (context : Context (eraseState initial).heap (eraseState initial).registers.b
      (E.vertices.map label) (GraphRelaxationRefinement.matrix adjacency) (es.map (encodeEdge label)) (label t) y.toList sw)
    (word : BoolList (eraseState initial).heap (eraseState initial).registers.c sw)
    (W : ℕ) (hW : 1 ≤ W) (hw : sw.length ≤ W) (labels : ∀ i,(label i).length ≤ W)
    (rowWidths : ∀ q∈y.toList,StoredBounded q W) :
    ∃ charge out,Run program
        (steps (E.vertices.map label) (GraphRelaxationRefinement.matrix adjacency)
          (es.map (encodeEdge label)) sw (label t) y.toList+1) charge initial [] out ∧
      StoredWalk (eraseState out).heap (eraseState out).registers.d
        (GraphRelaxationRefinement.encode label
          (BinaryFractionalWalkOracle.recover E adjacency (BinaryFractionalGraphOracle.outgoing y s) s t es).1) ∧
      SupportRecoveryProgram.Vertices (eraseState out).heap (eraseState initial).registers.a (E.vertices.map label) ∧
      Context (eraseState out).heap (eraseState initial).registers.b
        (E.vertices.map label) (GraphRelaxationRefinement.matrix adjacency) (es.map (encodeEdge label)) (label t) y.toList sw ∧
      BoolList (eraseState out).heap (eraseState initial).registers.c sw ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=591 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext ∧
        ext.length=cells (E.vertices.map label) (GraphRelaxationRefinement.matrix adjacency)
          (es.map (encodeEdge label)) sw (label t) y.toList) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 592 H A (recoveryCap n es.length W) := by
  have rows : n ≤ (GraphRelaxationRefinement.matrix adjacency).length := by
    simp [GraphRelaxationRefinement.matrix_length]
  have cols : ∀ (i : ℕ) (hi : i<n),
      n ≤ ((GraphRelaxationRefinement.matrix adjacency)[i]'(lt_of_lt_of_le hi rows)).length := by
    intro i hi
    exact (GraphRelaxationRefinement.matrix_row_length adjacency ⟨i,hi⟩).ge
  have hv : ∀ u∈E.vertices.map label,value u<n := by
    intro u hu
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hu
    rw [hlabel]
    exact i.isLt
  have ht : value (label t)<n := by rw [hlabel];exact t.isLt
  have valid := MaterializedGraphPath.indices_valid (recovered_encoding E adjacency es s t sw hsw label hlabel)
  have hn' : (eraseState initial).next=(eraseState initial).heap.length := by simpa [eraseState,State.map] using hn
  have empty' : (eraseState initial).stack=[] := by simp [eraseState,State.map,empty]
  obtain ⟨ext,root,len,high,rep⟩ := recover_high n (eraseState initial) pc0 hn' empty' input context word rows cols hv ht
    (by simpa using valid)
  obtain ⟨charge,out,run,erase,_,_,src⟩ := polynomial_simulation bounded high
  have stop : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase] at obs
    have halt : tickNatural program
        (state ((eraseState initial).heap++ext) ((eraseState initial).next+ext.length)
          (eraseState initial).registers.a (eraseState initial).registers.b
          (eraseState initial).registers.c root [] (eraseState initial).source 591)=none := by
      simp [tickNatural,program,state]
    rw [halt] at obs
    cases htick : tick program out with
    | none => rfl
    | some x => simp [htick] at obs
  have bound := steps_bound E adjacency es y s t sw hsw label hlabel W hW hw labels rowWidths
  have price := (terminal_accounting run bounded stop).2.trans
    (complete_mono 592 H A _ _ bound)
  refine ⟨charge,out,run,?_,?_,?_,?_,by simpa [state,eraseState,State.map] using src,
    ?_,?_,⟨ext,?_,len⟩,stop,price⟩
  · rw [erase]
    simpa only [state,result_eq E adjacency es y s t sw hsw label hlabel] using rep
  · rw [erase];exact GraphDiscoveryProgram.vertices_extend input ext
  · rw [erase];exact context_extend context ext
  · rw [erase];exact boolList_extend word ext
  · have h : (eraseState out).stack=[] := by rw [erase];rfl
    simpa [eraseState,State.map] using h
  · have h : (eraseState out).pc=591 := by rw [erase];rfl
    exact h
  · rw [erase];rfl

end DirectedFlowCutGap.CostedSupportProgram
