import DirectedFlowCutGap.OriginalDispatchExecution

namespace DirectedFlowCutGap.OriginalDispatch
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor IntegralNetworkFlow IntegralNetworkFlow.Tabulated

theorem dispatch_bit {n H A : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n) (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (ds : List (Fin n × Fin n))
    (initial : BitState 2140) (bounded : initial.Bounded H A) (pc0 : initial.pc=2138)
    (dense : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (hu : Table (eraseState initial).heap (eraseState initial).registers.a (ds.map fun e => (label e.1,label e.2)))
    (hc : Context (eraseState initial).heap (eraseState initial).registers.b
      (List.ofFn label) (IndexedRationalRead.fields costs.toList) (GraphRelaxationRefinement.matrix adjacency))
    (W : ℕ) (hW : 1≤W) (labels : ∀ i,(label i).length≤W) :
    ∃ charge out, Run program (steps (List.ofFn label) (IndexedRationalRead.fields costs.toList)
          (GraphRelaxationRefinement.matrix adjacency) (ds.map fun e => (label e.1,label e.2))+1) charge initial [] out ∧
      Result (eraseState out).heap (eraseState out).registers.d (encode label (BinaryFractionalDispatch.dispatch adjacency ds costs).1) ∧
      Table (eraseState out).heap (eraseState initial).registers.a (ds.map fun e => (label e.1,label e.2)) ∧
      Context (eraseState out).heap (eraseState initial).registers.b
        (List.ofFn label) (IndexedRationalRead.fields costs.toList) (GraphRelaxationRefinement.matrix adjacency) ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=2139 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext ∧ ext.length=cells (List.ofFn label) (IndexedRationalRead.fields costs.toList)
          (GraphRelaxationRefinement.matrix adjacency) (ds.map fun e => (label e.1,label e.2))) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 2140 H A
        (inputSteps (List.ofFn label) (IndexedRationalRead.fields costs.toList)
          (GraphRelaxationRefinement.matrix adjacency) (ds.map fun e => (label e.1,label e.2)) W) := by
  have dense' : (eraseState initial).next=(eraseState initial).heap.length := by
    simpa [eraseState,State.map] using dense
  have start : state (eraseState initial).heap (eraseState initial).next
      (eraseState initial).registers.a (eraseState initial).registers.b (eraseState initial).registers.c
      (eraseState initial).registers.d (eraseState initial).stack initial.source 2138=eraseState initial := by
    cases initial
    simp_all [eraseState,State.map,state]
  obtain ⟨ext,root,len,high,rep⟩ := dispatch adjacency costs label hlabel ds hu hc (eraseState initial).next
    (eraseState initial).registers.c (eraseState initial).registers.d dense'
    (eraseState initial).stack initial.source
  rw [start] at high
  have halt : tickNatural program (state ((eraseState initial).heap++ext)
      ((eraseState initial).next+ext.length) (eraseState initial).registers.a
      (eraseState initial).registers.b (eraseState initial).registers.c root
      (eraseState initial).stack initial.source 2139)=none := by simp [tickNatural,state,program]
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
      (SupportSearchEncoding.complete_mono 2140 H A _ _ (steps_bound adjacency costs label hlabel ds W hW labels))⟩
  · simpa only [erase,state] using rep
  · rw [erase];exact BinaryIndexedPairRead.table_extend hu ext
  · rw [erase];exact AvoidingDemandScan.context_extend hc ext
  · have h : (eraseState out).stack=(eraseState initial).stack := by rw [erase];rfl
    simpa [eraseState,State.map,empty] using h
  · have h : (eraseState out).pc=2139 := by rw [erase];rfl
    exact h
  · rw [erase];rfl

end DirectedFlowCutGap.OriginalDispatch
