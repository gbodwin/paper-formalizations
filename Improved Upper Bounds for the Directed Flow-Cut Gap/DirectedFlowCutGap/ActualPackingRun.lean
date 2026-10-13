import DirectedFlowCutGap.PackingRunExecution

namespace DirectedFlowCutGap.PackingRun
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram
open CanonicalRationalSum (StoredList)

/-- The actual original initialization followed by every represented-fuel step.
No initial packing state, intermediate oracle result, or output state is supplied. -/
theorem run_bit {n H A : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (capacity : Row n) (delta : Fraction) (label : Fin n → Bits)
    (numeric : ∀ i,value (label i)=i.val) (hn : 0<n)
    {xs : List DemandCollection.Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (DemandCollection.EncodesDemand label) xs ds)
    (fuel : Bits) (input fuelRoot : ℕ)
    (initial : BitState 7960) (bounded : initial.Bounded H A) (pc0 : initial.pc=7940)
    (dense : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (capRep : StoredList (eraseState initial).heap (eraseState initial).registers.a capacity.toList)
    (deltaRep : Stored (eraseState initial).heap (eraseState initial).registers.b delta)
    (inputRep : PackingStart.Input (eraseState initial).heap input label adjacency capacity xs)
    (contextRep : (eraseState initial).heap[(eraseState initial).registers.c]?=some (.pair input fuelRoot))
    (fuelRep : BoolList (eraseState initial).heap fuelRoot fuel)
    (B : ℕ) (hB : 1≤B) (labels : ∀ i,(label i).length≤B)
    (caps : ∀ x∈capacity.toList,StoredBounded x B) (scalarWidth : StoredBounded delta B) :
    ∃ steps charge out,Run program steps charge initial [] out ∧
      PackingStart.StateRecord (eraseState out).heap (eraseState out).registers.d label
        (BinaryFractionalCore.run capacity delta (BinaryFractionalGraphOracle.oracle adjacency ds capacity hn) fuel).state ∧
      out.source=initial.source ∧ out.stack=[] ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 7960 H A (instructionBound ds.length n B (value fuel) fuel.length) := by
  have dense' : (eraseState initial).next=(eraseState initial).heap.length := by
    simpa [eraseState,State.map] using dense
  have start : state (eraseState initial).heap (eraseState initial).next
      (eraseState initial).registers.a (eraseState initial).registers.b (eraseState initial).registers.c
      (eraseState initial).registers.d [] initial.source 7940=eraseState initial := by
    cases initial
    simp_all [eraseState,State.map,state]
  obtain ⟨steps,ext,first,root,high,rep,hb⟩ := full_run adjacency capacity delta label numeric hn
    encoded fuel capRep deltaRep inputRep contextRep fuelRep (eraseState initial).next dense' initial.source
    B hB labels caps scalarWidth
  rw [start] at high
  have halt : tickNatural program
      (state ((eraseState initial).heap++ext) ((eraseState initial).next+ext.length)
        (eraseState initial).registers.a first (eraseState initial).registers.c root [] initial.source 7945)=none := by
    have slot : program 7945=.halt := rfl
    simp only [tickNatural,state,slot]
  obtain ⟨charge,out,run,erase,_,_,source⟩ := polynomial_simulation bounded high
  have stop : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase,halt] at obs
    cases h : tick program out with
    | none => rfl
    | some r => simp [h] at obs
  refine ⟨steps,charge,out,run,?_,source,?_,⟨ext,?_⟩,stop,
    (terminal_accounting run bounded stop).2.trans (SupportSearchEncoding.complete_mono 7960 H A _ _ hb)⟩
  · rw [erase];exact rep
  · have h : (eraseState out).stack=[] := by rw [erase];rfl
    simpa [eraseState,State.map] using h
  · rw [erase];rfl
end DirectedFlowCutGap.PackingRun
