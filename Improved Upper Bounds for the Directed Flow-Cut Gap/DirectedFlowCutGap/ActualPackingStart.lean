import DirectedFlowCutGap.PackingStartBounds

namespace DirectedFlowCutGap.PackingStart
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

/-- The same physical run constructs initial weights, calls the actual graph
oracle, normalizes, evaluates the objective and allocates every initial state
field. Original graph/input representations and widths are its only data premises. -/
theorem start_bit {n H A : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (capacity : Row n) (delta : Fraction) (label : Fin n → Bits)
    (hlabel : ∀ i,value (label i)=i.val) (hn : 0<n)
    {xs : List DemandCollection.Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (DemandCollection.EncodesDemand label) xs ds)
    (initialState : BitState 3060) (bounded : initialState.Bounded H A) (pc0 : initialState.pc=3020)
    (dense : value initialState.next=initialState.heap.length) (empty : initialState.stack=[])
    (row : StoredList (eraseState initialState).heap (eraseState initialState).registers.a capacity.toList)
    (scalar : Stored (eraseState initialState).heap (eraseState initialState).registers.b delta)
    (input : Input (eraseState initialState).heap (eraseState initialState).registers.c label adjacency capacity xs)
    (B : ℕ) (hB : 1≤B) (labels : ∀ i,(label i).length≤B) (deltaWidth : StoredBounded delta B)
    (rowWidth : ∀ x∈capacity.toList,StoredBounded x B) :
    ∃ steps charge out,Run program steps charge initialState [] out ∧
      StateRecord (eraseState out).heap (eraseState out).registers.d label
        (BinaryFractionalCore.start capacity delta (BinaryFractionalGraphOracle.oracle adjacency ds capacity hn)).1 ∧
      out.source=initialState.source ∧ out.stack=[] ∧ out.pc=3057 ∧
      (∃ ext,(eraseState out).heap=(eraseState initialState).heap++ext) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 3060 H A (instructionBound ds.length n B) := by
  have dense' : (eraseState initialState).next=(eraseState initialState).heap.length := by
    simpa [eraseState,State.map] using dense
  have empty' : (eraseState initialState).stack=[] := by simp [eraseState,State.map,empty]
  obtain ⟨ot,final,high,source,stack,pc,_,ext,rep,ob⟩ :=
    start_high adjacency capacity delta label hlabel hn encoded (eraseState initialState) pc0 dense' empty' row scalar input
  have hb := start_steps_bound adjacency capacity delta label hn ds ot B hB labels deltaWidth rowWidth ob
  obtain ⟨charge,out,run,erase,_,_,src⟩ := polynomial_simulation bounded high
  have stop : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase] at obs
    have ht : tickNatural program final=none := by simp [tickNatural,pc,program]
    rw [ht] at obs
    cases h : tick program out with
    | none => rfl
    | some r => simp [h] at obs
  refine ⟨_,charge,out,run,?_,src.trans source,?_,?_,?_,stop,
    (terminal_accounting run bounded stop).2.trans (SupportSearchEncoding.complete_mono 3060 H A _ _ hb)⟩
  · rw [erase];exact rep
  · have h : (eraseState out).stack=[] := by rw [erase];exact stack
    simpa [eraseState,State.map] using h
  · have h : (eraseState out).pc=3057 := by rw [erase];exact pc
    exact h
  · rw [erase];exact ext
end DirectedFlowCutGap.PackingStart
