import DirectedFlowCutGap.PreparedPackingExecution

namespace DirectedFlowCutGap.PreparedPacking
open BinaryArithmetic BinaryRational BinaryFractionalRows ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor
open CanonicalRationalSum (StoredList)

/-- Primitive represented input lists suffice: the actual machine allocates all
composite metadata, derives its parameters, initializes and iterates the state. -/
theorem solve_primitives_bit {n H A : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (capacity : Row n) (label : Fin n → Bits)
    (numeric : ∀ i,value (label i)=i.val) (hn : 0<n)
    {xs : List DemandCollection.Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (DemandCollection.EncodesDemand label) xs ds)
    (initial : BitState 8360) (bounded : initial.Bounded H A) (pc0 : initial.pc=8348)
    (dense : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (capRep : StoredList (eraseState initial).heap (eraseState initial).registers.a capacity.toList)
    (verts : GraphDiscoveryProgram.Vertices (eraseState initial).heap (eraseState initial).registers.b
      ((List.finRange n).map label))
    (graph : GraphAdjacencyProgram.Matrix (eraseState initial).heap (eraseState initial).registers.c
      (GraphRelaxationRefinement.matrix adjacency))
    (pairs : DemandCollection.DemandList (eraseState initial).heap (eraseState initial).registers.d xs)
    (B : ℕ) (labels : ∀ i,(label i).length≤B)
    (caps : ∀ x∈capacity.toList,StoredBounded x B) :
    ∃ k charge out, Run program k charge initial [] out ∧
      PackingStart.StateRecord (eraseState out).heap (eraseState out).registers.d label
        (BinaryFractionalCore.solveInput capacity (BinaryFractionalGraphOracle.oracle adjacency ds capacity hn)).state ∧
      StoredList (eraseState out).heap (eraseState initial).registers.a capacity.toList ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=8350 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 8360 H A (instructionBound ds.length n B) := by
  have dense' : (eraseState initial).next=(eraseState initial).heap.length := by
    simpa [eraseState,State.map] using dense
  have start : state (eraseState initial).heap (eraseState initial).next
      (eraseState initial).registers.a (eraseState initial).registers.b (eraseState initial).registers.c
      (eraseState initial).registers.d [] initial.source 8348=eraseState initial := by
    cases initial
    simp_all [eraseState,State.map,state]
  obtain ⟨k,ext,root,high,rep,bound⟩ := solve_primitives adjacency capacity label numeric hn encoded
    capRep verts graph pairs (eraseState initial).next dense' initial.source B labels caps
  rw [start] at high
  have halt : tickNatural program (state ((eraseState initial).heap++ext)
      ((eraseState initial).next+ext.length) (eraseState initial).registers.a
      ((eraseState initial).next+3) (eraseState initial).registers.c root [] initial.source 8350)=none := by
    simp [tickNatural,state,program]
  obtain ⟨charge,out,run,erase,_,_,sourceOut⟩ := polynomial_simulation bounded high
  have stop : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase,halt] at obs
    cases h : tick program out with
    | none => rfl
    | some r => simp [h] at obs
  refine ⟨k,charge,out,run,?_,?_,sourceOut,?_,?_,⟨ext,?_⟩,stop,
    (terminal_accounting run bounded stop).2.trans
      (SupportSearchEncoding.complete_mono 8360 H A _ _ bound)⟩
  · simpa only [erase,state] using rep
  · rw [erase];exact CanonicalRationalSum.list_extend capRep ext
  · have h : (eraseState out).stack=[] := by rw [erase];rfl
    simpa [eraseState,State.map] using h
  · have h : (eraseState out).pc=8350 := by rw [erase];rfl
    exact h
  · rw [erase];rfl
end DirectedFlowCutGap.PreparedPacking
