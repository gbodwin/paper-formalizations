import DirectedFlowCutGap.AvoidingKeptPathExecution

namespace DirectedFlowCutGap.AvoidingKeptPath
open BinaryArithmetic IntegralNetworkFlow IntegralNetworkFlow.Tabulated ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor

theorem search_bit {n H A : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n) (s t : Fin n)
    (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (initial : BitState 1800) (bounded : initial.Bounded H A) (pc0 : initial.pc=1798)
    (dense : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (hu : GraphDiscoveryProgram.Vertices (eraseState initial).heap (eraseState initial).registers.a (List.ofFn label))
    (hc : KeptAdjacencyInput.Context (eraseState initial).heap (eraseState initial).registers.b
      (label s) (label t) (IndexedRationalRead.fields costs.toList) (GraphRelaxationRefinement.matrix adjacency))
    (W : ℕ) (hW : 1≤W) (labels : ∀ i,(label i).length≤W) :
    ∃ charge out, Run program (steps (label s) (label t) (List.ofFn label) (IndexedRationalRead.fields costs.toList) (GraphRelaxationRefinement.matrix adjacency)+1)
      charge initial [] out ∧
      GraphDiscoveryProgram.StoredOption (eraseState out).heap (eraseState out).registers.d
        ((BinaryFractionalWalkOracle.shortest (ResidualSearch.Enumeration.fin n)
          (BinaryFractionalDispatch.keptAdjacency adjacency (BinaryFractionalDispatch.zeroMask costs).1 s t).1 (fun _ => (BinaryRational.zero,1)) s t).1.map
          (GraphRelaxationRefinement.encode label)) ∧
      GraphDiscoveryProgram.Vertices (eraseState out).heap (eraseState initial).registers.a (List.ofFn label) ∧
      KeptAdjacencyInput.Context (eraseState out).heap (eraseState initial).registers.b
        (label s) (label t) (IndexedRationalRead.fields costs.toList) (GraphRelaxationRefinement.matrix adjacency) ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=1799 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext ∧
        ext.length=cells (label s) (label t) (List.ofFn label) (IndexedRationalRead.fields costs.toList) (GraphRelaxationRefinement.matrix adjacency)) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 1800 H A
        (inputSteps (label s) (label t) (List.ofFn label) (IndexedRationalRead.fields costs.toList)
          (GraphRelaxationRefinement.matrix adjacency) W) := by
  have dense' : (eraseState initial).next=(eraseState initial).heap.length := by
    simpa [eraseState,State.map] using dense
  have start : state (eraseState initial).heap (eraseState initial).next
      (eraseState initial).registers.a (eraseState initial).registers.b (eraseState initial).registers.c
      (eraseState initial).registers.d (eraseState initial).stack initial.source 1798=eraseState initial := by
    cases initial
    simp_all [eraseState,State.map,state]
  obtain ⟨ext,root,len,high,rep⟩ := search adjacency costs s t label hlabel hu hc (eraseState initial).next
    (eraseState initial).registers.c (eraseState initial).registers.d dense'
    (eraseState initial).stack initial.source
  rw [start] at high
  have halt : tickNatural program (state ((eraseState initial).heap++ext)
      ((eraseState initial).next+ext.length) (eraseState initial).registers.a
      (eraseState initial).registers.b (eraseState initial).registers.c root
      (eraseState initial).stack initial.source 1799)=none := by simp [tickNatural,state,program]
  obtain ⟨charge,out,run,erase,_,_,sourceOut⟩ := polynomial_simulation bounded high
  have stop : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase,halt] at obs
    cases h : tick program out with
    | none => rfl
    | some r => simp [h] at obs
  refine ⟨charge,out,run,?_,?_,?_,sourceOut,?_,?_,⟨ext,?_,len⟩,stop,
    (terminal_accounting run bounded stop).2.trans
      (SupportSearchEncoding.complete_mono 1800 H A _ _ (steps_bound adjacency costs s t label hlabel W hW labels))⟩
  · simpa only [erase,state] using rep
  · rw [erase];exact GraphDiscoveryProgram.vertices_extend hu ext
  · rw [erase];exact KeptAdjacencyInput.context_extend hc ext
  · have h : (eraseState out).stack=(eraseState initial).stack := by rw [erase];rfl
    simpa [eraseState,State.map,empty] using h
  · have h : (eraseState out).pc=1799 := by rw [erase];rfl
    exact h
  · rw [erase];rfl

end DirectedFlowCutGap.AvoidingKeptPath
