import DirectedFlowCutGap.PackingRunStartCall

namespace DirectedFlowCutGap.PackingRun
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor
open CanonicalRationalSum (StoredList)

theorem iteration_return {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (capacity : Row n) (s : BinaryFractionalCore.State n) (label : Fin n → Bits)
    (numeric : ∀ i,value (label i)=i.val) (hn : 0<n)
    {xs : List DemandCollection.Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (DemandCollection.EncodesDemand label) xs ds)
    {heap : NaturalHeap} {cap original context input fuelRoot d : ℕ} (fuel : Bits)
    (capRep : StoredList heap cap capacity.toList) (stateRep : PackingStart.StateRecord heap original label s)
    (inputRep : PackingStart.Input heap input label adjacency capacity xs)
    (contextRep : heap[context]?=some (.pair input fuelRoot)) (fuelRep : BoolList heap fuelRoot fuel)
    (next : ℕ) (dense : next=heap.length) (source : Bits)
    (B : ℕ) (hB : 1≤B) (labels : ∀ i,(label i).length≤B)
    (caps : ∀ x∈capacity.toList,StoredBounded x B)
    (weights : ∀ x∈s.weights.toList,StoredBounded x B) (loads : ∀ x∈s.loads.toList,StoredBounded x B)
    (total : StoredBounded s.total B) (cost : StoredBounded s.bestCost B)
    (saved : Registers ℕ) (pc : Fin 7960) (stack : List (Frame ℕ 7960)) :
    ∃ k ext root,
      NaturalRun program (k+1)
        (state heap next cap original context d (⟨pc,.r3,saved⟩::stack) source 7880) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      PackingStart.StateRecord (heap++ext) root label
        (BinaryFractionalCore.runFrom capacity (BinaryFractionalGraphOracle.oracle adjacency ds capacity hn) fuel s).state ∧
      k ≤ PackingIteration.instructionBound ds.length n B (value fuel) fuel.length := by
  obtain ⟨k,ext,out,run,he,nd,st,src,outpc,rep,bound⟩ := PackingIteration.full_bounded adjacency capacity s label numeric hn encoded
    fuel capRep stateRep inputRep contextRep fuelRep next dense source B hB labels caps weights loads total cost
  have terminal : PackingIteration.program out.pc=.halt := by
    rw [outpc]
    norm_num [PackingIteration.program]
  have lifted := child_return iterationLabel PackingIteration.program iteration_slots run rfl st
    .r3 .r3 saved pc stack (iteration_halt out.pc terminal)
  have entry : iterationLabel 4820=(7880 : Fin 7960) := by decide
  refine ⟨k,ext,out.registers.d,?_,?_,bound⟩
  · simpa only [PackingIteration.state,entry,state,he,nd,src,Registers.set,Registers.get] using lifted
  · simpa only [he] using rep
end DirectedFlowCutGap.PackingRun
