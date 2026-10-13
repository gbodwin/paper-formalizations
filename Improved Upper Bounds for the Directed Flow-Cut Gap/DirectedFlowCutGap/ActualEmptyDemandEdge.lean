import DirectedFlowCutGap.EmptyDemandEdgeExecution

namespace DirectedFlowCutGap.EmptyDemandEdge
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor

theorem scan_bit {H A : ℕ} {u v : Bits} {rows : List Bits}
    (initial : BitState 128) (bounded : initial.Bounded H A) (pc0 : initial.pc=126)
    (dense : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (hu : Demand (eraseState initial).heap (eraseState initial).registers.a u v)
    (hc : GraphAdjacencyProgram.Matrix (eraseState initial).heap (eraseState initial).registers.b rows)
    (hi : value u<rows.length) (hj : value v<(rows[value u]).length) :
    ∃ charge out, Run program (steps u v+1) charge initial [] out ∧
      (eraseState out).heap[(eraseState out).registers.d]?=some (.flag (bit rows u v)) ∧
      Demand (eraseState out).heap (eraseState initial).registers.a u v ∧
      GraphAdjacencyProgram.Matrix (eraseState out).heap (eraseState initial).registers.b rows ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=127 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext ∧ ext.length=cells u v) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 128 H A
        (inputSteps rows u v) := by
  have dense' : (eraseState initial).next=(eraseState initial).heap.length := by
    simpa [eraseState,State.map] using dense
  have start : state (eraseState initial).heap (eraseState initial).next
      (eraseState initial).registers.a (eraseState initial).registers.b (eraseState initial).registers.c
      (eraseState initial).registers.d (eraseState initial).stack initial.source 126=eraseState initial := by
    cases initial
    simp_all [eraseState,State.map,state]
  obtain ⟨ext,root,len,high,rep⟩ := scan hu hc hi hj (eraseState initial).next
    (eraseState initial).registers.c (eraseState initial).registers.d dense'
    (eraseState initial).stack initial.source
  rw [start] at high
  have halt : tickNatural program (state ((eraseState initial).heap++ext)
      ((eraseState initial).next+ext.length) (eraseState initial).registers.a
      (eraseState initial).registers.b (eraseState initial).registers.c root
      (eraseState initial).stack initial.source 127)=none := by simp [tickNatural,state,program]
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
      (SupportSearchEncoding.complete_mono 128 H A _ _ (steps_bound rows u v hi hj))⟩
  · simpa only [erase,state] using rep
  · rw [erase];exact demand_extend hu ext
  · rw [erase];exact GraphAdjacencyProgram.matrix_extend hc ext
  · have h : (eraseState out).stack=(eraseState initial).stack := by rw [erase];rfl
    simpa [eraseState,State.map,empty] using h
  · have h : (eraseState out).pc=127 := by rw [erase];rfl
    exact h
  · rw [erase];rfl

end DirectedFlowCutGap.EmptyDemandEdge
