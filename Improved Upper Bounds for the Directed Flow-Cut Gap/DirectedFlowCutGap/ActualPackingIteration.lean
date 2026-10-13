import DirectedFlowCutGap.PackingIterationBound

namespace DirectedFlowCutGap.PackingIteration
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

/-- Actual complete finite iteration, with represented binary fuel converted by
instructions and every adaptive state update executed on the same heap. The
paid physical bound is polynomial in numerical fuel and original field widths. -/
theorem iterate_bit {n H A : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (capacity : Row n) (s : BinaryFractionalCore.State n) (label : Fin n → Bits)
    (numeric : ∀ i,value (label i)=i.val) (hn : 0<n)
    {xs : List DemandCollection.Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (DemandCollection.EncodesDemand label) xs ds)
    (fuel : Bits) (input fuelRoot : ℕ)
    (initial : BitState 4860) (bounded : initial.Bounded H A) (pc0 : initial.pc=4820)
    (dense : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (capRep : StoredList (eraseState initial).heap (eraseState initial).registers.a capacity.toList)
    (stateRep : PackingStart.StateRecord (eraseState initial).heap (eraseState initial).registers.b label s)
    (inputRep : PackingStart.Input (eraseState initial).heap input label adjacency capacity xs)
    (contextRep : (eraseState initial).heap[(eraseState initial).registers.c]?=some (.pair input fuelRoot))
    (fuelRep : BoolList (eraseState initial).heap fuelRoot fuel)
    (B : ℕ) (hB : 1≤B) (labels : ∀ i,(label i).length≤B)
    (caps : ∀ x∈capacity.toList,StoredBounded x B)
    (weights : ∀ x∈s.weights.toList,StoredBounded x B)
    (cost : StoredBounded s.bestCost B) (total : StoredBounded s.total B)
    (loads : ∀ x∈s.loads.toList,StoredBounded x B) :
    ∃ steps charge out,Run program steps charge initial [] out ∧
      PackingStart.StateRecord (eraseState out).heap (eraseState out).registers.d label
        (BinaryFractionalCore.runFrom capacity (BinaryFractionalGraphOracle.oracle adjacency ds capacity hn) fuel s).state ∧
      out.source=initial.source ∧ out.stack=[] ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 4860 H A (instructionBound ds.length n B (value fuel) fuel.length) := by
  have dense' : (eraseState initial).next=(eraseState initial).heap.length := by
    simpa [eraseState,State.map] using dense
  have start : state (eraseState initial).heap (eraseState initial).next
      (eraseState initial).registers.a (eraseState initial).registers.b (eraseState initial).registers.c
      (eraseState initial).registers.d [] initial.source 4820=eraseState initial := by
    cases initial
    simp_all [eraseState,State.map,state]
  obtain ⟨steps,ext,final,high,he,_,hst,src,pc,rep,hb⟩ := full_bounded adjacency capacity s label numeric hn
    encoded fuel capRep stateRep inputRep contextRep fuelRep (eraseState initial).next dense' initial.source
    B hB labels caps weights loads total cost
  rw [start] at high
  have halt : tickNatural program final=none := by
    have slot : program 4859=.halt := rfl
    simp only [tickNatural,pc,slot]
  obtain ⟨charge,out,run,erase,_,_,source⟩ := polynomial_simulation bounded high
  have stop : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase,halt] at obs
    cases h : tick program out with
    | none => rfl
    | some r => simp [h] at obs
  refine ⟨steps,charge,out,run,?_,source.trans src,?_,⟨ext,?_⟩,stop,
    (terminal_accounting run bounded stop).2.trans (SupportSearchEncoding.complete_mono 4860 H A _ _ hb)⟩
  · rw [erase];exact rep
  · have h : (eraseState out).stack=[] := by rw [erase];exact hst
    simpa [eraseState,State.map] using h
  · rw [erase];exact he
end DirectedFlowCutGap.PackingIteration
