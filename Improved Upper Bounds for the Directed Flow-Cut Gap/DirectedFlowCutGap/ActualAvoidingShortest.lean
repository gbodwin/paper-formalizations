import DirectedFlowCutGap.AvoidingShortestExecution

namespace DirectedFlowCutGap.AvoidingShortest
open BinaryArithmetic IntegralNetworkFlow IntegralNetworkFlow.Tabulated ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor

theorem search_bit {n H A : ℕ} (E : ResidualSearch.Enumeration (Fin n))
    (adjacency : BinaryFractionalWalkOracle.Adjacency n) (s t : Fin n)
    (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (initial : BitState 1440) (bounded : initial.Bounded H A) (pc0 : initial.pc=1438)
    (dense : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (hu : GraphDiscoveryProgram.Vertices (eraseState initial).heap (eraseState initial).registers.a (E.vertices.map label))
    (hc : AvoidingZeroContext.Static (eraseState initial).heap (eraseState initial).registers.b
      (GraphRelaxationRefinement.matrix adjacency) (label s) (label t))
    (W : ℕ) (hW : 1≤W) (labels : ∀ i,(label i).length≤W) :
    ∃ charge out, Run program (steps (E.vertices.map label) (GraphRelaxationRefinement.matrix adjacency) (label s) (label t)+1)
      charge initial [] out ∧
      GraphDiscoveryProgram.StoredOption (eraseState out).heap (eraseState out).registers.d
        ((BinaryFractionalWalkOracle.shortest E adjacency (fun _ => (BinaryRational.zero,1)) s t).1.map
          (GraphRelaxationRefinement.encode label)) ∧
      GraphDiscoveryProgram.Vertices (eraseState out).heap (eraseState initial).registers.a (E.vertices.map label) ∧
      AvoidingZeroContext.Static (eraseState out).heap (eraseState initial).registers.b
        (GraphRelaxationRefinement.matrix adjacency) (label s) (label t) ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=1439 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext ∧
        ext.length=cells (E.vertices.map label) (GraphRelaxationRefinement.matrix adjacency) (label s) (label t)) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 1440 H A
        (inputSteps n W (label s).length) := by
  have dense' : (eraseState initial).next=(eraseState initial).heap.length := by
    simpa [eraseState,State.map] using dense
  have start : state (eraseState initial).heap (eraseState initial).next
      (eraseState initial).registers.a (eraseState initial).registers.b (eraseState initial).registers.c
      (eraseState initial).registers.d (eraseState initial).stack initial.source 1438=eraseState initial := by
    cases initial
    simp_all [eraseState,State.map,state]
  obtain ⟨ext,root,len,high,rep⟩ := search E adjacency s t label hlabel hu hc (eraseState initial).next
    (eraseState initial).registers.c (eraseState initial).registers.d dense'
    (eraseState initial).stack initial.source
  rw [start] at high
  have halt : tickNatural program (state ((eraseState initial).heap++ext)
      ((eraseState initial).next+ext.length) (eraseState initial).registers.a
      (eraseState initial).registers.b (eraseState initial).registers.c root
      (eraseState initial).stack initial.source 1439)=none := by simp [tickNatural,state,program]
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
      (SupportSearchEncoding.complete_mono 1440 H A _ _ (steps_bound E adjacency s t label hlabel W hW labels))⟩
  · simpa only [erase,state] using rep
  · rw [erase];exact GraphDiscoveryProgram.vertices_extend hu ext
  · rw [erase];exact AvoidingZeroContext.static_extend hc ext
  · have h : (eraseState out).stack=(eraseState initial).stack := by rw [erase];rfl
    simpa [eraseState,State.map,empty] using h
  · have h : (eraseState out).pc=1439 := by rw [erase];rfl
    exact h
  · rw [erase];rfl

end DirectedFlowCutGap.AvoidingShortest
