import DirectedFlowCutGap.PackingCompleteExecution

namespace DirectedFlowCutGap.PackingComplete
open BinaryArithmetic BinaryRational BinaryFractionalRows ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor
open BooleanTableRead (BoolList)
open CanonicalRationalSum (StoredList)
open RationalComparisonProgram (Stored)

/-- The complete packing machine constructs its own dimension, delta and polynomial
fuel, initializes the real state, and executes the exact old solveInput result. -/
theorem solve_input_bit {n H A : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (capacity : Row n) (label : Fin n → Bits)
    (numeric : ∀ i,value (label i)=i.val) (hn : 0<n)
    {xs : List DemandCollection.Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (DemandCollection.EncodesDemand label) xs ds)
    (initial : BitState 8340) (bounded : initial.Bounded H A) (pc0 : initial.pc=8320)
    (dense : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (capRep : StoredList (eraseState initial).heap (eraseState initial).registers.a capacity.toList)
    (inputRep : PackingStart.Input (eraseState initial).heap (eraseState initial).registers.b label adjacency capacity xs)
    (B : ℕ) (labels : ∀ i,(label i).length≤B)
    (caps : ∀ x∈capacity.toList,StoredBounded x B) :
    ∃ k charge out, Run program k charge initial [] out ∧
      PackingStart.StateRecord (eraseState out).heap (eraseState out).registers.d label
        (BinaryFractionalCore.solveInput capacity (BinaryFractionalGraphOracle.oracle adjacency ds capacity hn)).state ∧
      StoredList (eraseState out).heap (eraseState initial).registers.a capacity.toList ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=8326 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 8340 H A (instructionBound ds.length n B) := by
  have dense' : (eraseState initial).next=(eraseState initial).heap.length := by
    simpa [eraseState,State.map] using dense
  have start : state (eraseState initial).heap (eraseState initial).next
      (eraseState initial).registers.a (eraseState initial).registers.b (eraseState initial).registers.c
      (eraseState initial).registers.d [] initial.source 8320=eraseState initial := by
    cases initial
    simp_all [eraseState,State.map,state]
  obtain ⟨k,ext,highOut,high,heap,next,stack,source,pc,rep,bound⟩ := solve_input adjacency capacity label numeric hn encoded capRep inputRep
    (eraseState initial).next dense' initial.source B labels caps
  rw [start] at high
  have halt : tickNatural program highOut=none := by
    have slot : program 8326=.halt := rfl
    simp only [tickNatural,pc,slot]
  obtain ⟨charge,out,run,erase,_,_,sourceOut⟩ := polynomial_simulation bounded high
  have stop : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase,halt] at obs
    cases h : tick program out with
    | none => rfl
    | some r => simp [h] at obs
  refine ⟨k,charge,out,run,?_,?_,sourceOut.trans source,?_,?_,⟨ext,?_⟩,stop,
    (terminal_accounting run bounded stop).2.trans
      (SupportSearchEncoding.complete_mono 8340 H A _ _ bound)⟩
  · rw [erase];exact rep
  · rw [erase,heap];exact CanonicalRationalSum.list_extend capRep ext
  · have h : (eraseState out).stack=[] := by rw [erase];exact stack
    simpa [eraseState,State.map] using h
  · have h : (eraseState out).pc=8326 := by rw [erase];exact pc
    exact h
  · rw [erase];exact heap
end DirectedFlowCutGap.PackingComplete
