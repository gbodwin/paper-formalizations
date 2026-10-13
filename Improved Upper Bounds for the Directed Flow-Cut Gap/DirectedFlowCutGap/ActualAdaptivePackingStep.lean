import DirectedFlowCutGap.AdaptivePackingStepBounds

namespace DirectedFlowCutGap.AdaptivePackingState
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

/-- A complete actual adaptive step, including its paid terminal attempt. The
original represented graph, demands, current state and field widths are inputs;
no selected choice, amount, normalized row or intermediate state is supplied. -/
theorem step_bit {n H A : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (capacity : Row n) (s : BinaryFractionalCore.State n) (label : Fin n → Bits)
    (numeric : ∀ i,value (label i)=i.val) (hn : 0<n)
    {xs : List DemandCollection.Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (DemandCollection.EncodesDemand label) xs ds)
    (initial : BitState 4800) (bounded : initial.Bounded H A) (pc0 : initial.pc=4400)
    (dense : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (capRep : StoredList (eraseState initial).heap (eraseState initial).registers.a capacity.toList)
    (stateRep : PackingStart.StateRecord (eraseState initial).heap (eraseState initial).registers.b label s)
    (inputRep : PackingStart.Input (eraseState initial).heap (eraseState initial).registers.c label adjacency capacity xs)
    (B : ℕ) (hB : 1≤B) (labels : ∀ i,(label i).length≤B)
    (caps : ∀ x∈capacity.toList,StoredBounded x B)
    (weights : ∀ x∈s.weights.toList,StoredBounded x B)
    (cost : StoredBounded s.bestCost B) (total : StoredBounded s.total B)
    (loads : ∀ x∈s.loads.toList,StoredBounded x B) :
    ∃ steps charge out,Run program steps charge initial [] out ∧
      PackingStart.StateRecord (eraseState out).heap (eraseState out).registers.d label
        (BinaryFractionalCore.step capacity (BinaryFractionalGraphOracle.oracle adjacency ds capacity hn) s).1 ∧
      out.source=initial.source ∧ out.stack=[] ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 4800 H A (instructionBound ds.length n B) := by
  have dense' : (eraseState initial).next=(eraseState initial).heap.length := by
    simpa [eraseState,State.map] using dense
  have start : state (eraseState initial).heap (eraseState initial).next
      (eraseState initial).registers.a (eraseState initial).registers.b (eraseState initial).registers.c
      (eraseState initial).registers.d [] initial.source 4400=eraseState initial := by
    cases initial
    simp_all [eraseState,State.map,state]
  obtain ⟨steps,ext,final,high,he,_,hst,src,halt,rep,ob⟩ := step_execution adjacency capacity s label numeric hn
    encoded capRep stateRep inputRep (eraseState initial).next dense' initial.source
  rw [start] at high
  have caps' : ∀ i,StoredBounded (get capacity i) B := by
    intro i
    apply caps
    rw [ScalarQuotientRow.row_toList]
    exact List.mem_ofFn.mpr ⟨i,rfl⟩
  have hb := (ob B hB labels weights caps').trans
    (work_bound ds.length capacity s _ label numeric B labels caps weights cost total loads)
  obtain ⟨charge,out,run,erase,_,_,source⟩ := polynomial_simulation bounded high
  have stop : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase,halt] at obs
    cases h : tick program out with
    | none => rfl
    | some r => simp [h] at obs
  refine ⟨steps,charge,out,run,?_,source.trans src,?_,⟨ext,?_⟩,stop,
    (terminal_accounting run bounded stop).2.trans (SupportSearchEncoding.complete_mono 4800 H A _ _ hb)⟩
  · rw [erase];exact rep
  · have h : (eraseState out).stack=[] := by rw [erase];exact hst
    simpa [eraseState,State.map] using h
  · rw [erase];exact he
end DirectedFlowCutGap.AdaptivePackingState
