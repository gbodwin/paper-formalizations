import DirectedFlowCutGap.GraphRecoveryExecution
import DirectedFlowCutGap.GraphRecoveryBounds

/-! A single lower-machine run constructs the synchronous minimizer, branches
on its actual presence, builds the support-search context from that returned
record, recovers the literal simple path and computes its exact graph cost.
Initial graph representations and width bounds remain explicit. -/
namespace DirectedFlowCutGap.GraphRecoveryController
open BinaryArithmetic BinaryRational BinaryFractionalRows IntegralNetworkFlow IntegralNetworkFlow.Tabulated
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open GraphWalkExtension

theorem graph_bit {n H A : ℕ} (E : ResidualSearch.Enumeration (Fin n))
    (adjacency : BinaryFractionalWalkOracle.Adjacency n) (y : Row n) (s t : Fin n)
    (sw : Bits) (hs : value sw=s.val) (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (initial : BitState 1344) (bounded : initial.Bounded H A)
    (pc0 : initial.pc=1342) (hn : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (input : GraphDiscoveryProgram.Vertices (eraseState initial).heap (eraseState initial).registers.a
      (E.vertices.map label))
    (context : GraphDiscoveryProgram.GlobalContext (eraseState initial).heap (eraseState initial).registers.b
      (E.vertices.map label) (GraphRelaxationRefinement.matrix adjacency) y.toList sw (label t))
    (word : BoolList (eraseState initial).heap (eraseState initial).registers.c (label s))
    (W : ℕ) (hW : 1 ≤ W) (hw : sw.length ≤ W) (labels : ∀ i,(label i).length ≤ W)
    (rowWidths : ∀ q∈y.toList,StoredBounded q W) :
    ∃ charge out,Run program
        (steps (E.vertices.map label) (GraphRelaxationRefinement.matrix adjacency)
          y.toList sw (label t) (label s)+1) charge initial [] out ∧
      GraphDiscoveryProgram.StoredOption (eraseState out).heap (eraseState out).registers.d
        ((BinaryFractionalWalkOracle.shortest E adjacency (BinaryFractionalGraphOracle.outgoing y s) s t).1.map
          (GraphRelaxationRefinement.encode label)) ∧
      GraphDiscoveryProgram.Vertices (eraseState out).heap (eraseState initial).registers.a (E.vertices.map label) ∧
      GraphDiscoveryProgram.GlobalContext (eraseState out).heap (eraseState initial).registers.b
        (E.vertices.map label) (GraphRelaxationRefinement.matrix adjacency) y.toList sw (label t) ∧
      BoolList (eraseState out).heap (eraseState initial).registers.c (label s) ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=1343 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext ∧
        ext.length=cells (E.vertices.map label) (GraphRelaxationRefinement.matrix adjacency)
          y.toList sw (label t) (label s)) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 1344 H A (instructionBound n W sw.length) := by
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
  have hc : ∀ u∈E.vertices.map label,value u<y.toList.length := by simpa only [Vector.length_toList] using hv
  have hn' : (eraseState initial).next=(eraseState initial).heap.length := by simpa [eraseState,State.map] using hn
  have empty' : (eraseState initial).stack=[] := by simp [eraseState,State.map,empty]
  obtain ⟨ext,root,len,high,rep⟩ := shortest_high n (eraseState initial) pc0 hn' empty' input context word rows cols hv ht hc
    (recovery_valid E adjacency y s t sw hs label hlabel)
  obtain ⟨charge,out,run,erase,_,_,src⟩ := polynomial_simulation bounded high
  have stop : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase] at obs
    have halt : tickNatural program
        (state ((eraseState initial).heap++ext) ((eraseState initial).next+ext.length)
          (eraseState initial).registers.a (eraseState initial).registers.b
          (eraseState initial).registers.c root [] (eraseState initial).source 1343)=none := by
      simp [tickNatural,program,state]
    rw [halt] at obs
    cases htick : tick program out with
    | none => rfl
    | some x => simp [htick] at obs
  have bound := steps_bound E adjacency y s t sw hs label hlabel W hW hw labels rowWidths
  have price := (terminal_accounting run bounded stop).2.trans
    (SupportSearchEncoding.complete_mono 1344 H A _ _ bound)
  refine ⟨charge,out,run,?_,?_,?_,?_,by simpa [state,eraseState,State.map] using src,
    ?_,?_,⟨ext,?_,len⟩,stop,price⟩
  · rw [erase]
    simpa only [state,result_eq E adjacency y s t sw hs label hlabel] using rep
  · rw [erase];exact GraphDiscoveryProgram.vertices_extend input ext
  · rw [erase];exact GraphDiscoveryProgram.global_extend context ext
  · rw [erase];exact boolList_extend word ext
  · have h : (eraseState out).stack=[] := by rw [erase];rfl
    simpa [eraseState,State.map] using h
  · have h : (eraseState out).pc=1343 := by rw [erase];rfl
    exact h
  · rw [erase];rfl

end DirectedFlowCutGap.GraphRecoveryController
