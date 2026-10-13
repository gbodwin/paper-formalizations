import DirectedFlowCutGap.PackingCompleteParametersCall

namespace DirectedFlowCutGap.PackingComplete
open BinaryArithmetic BinaryRational BinaryFractionalRows ImmutableReferenceSimulation
open BooleanTableRead (BoolList)
open CanonicalRationalSum (StoredList)
open RationalComparisonProgram (Stored)

theorem run_return {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (capacity : Row n) (delta : Fraction) (label : Fin n → Bits)
    (numeric : ∀ i,value (label i)=i.val) (hn : 0<n)
    {xs : List DemandCollection.Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (DemandCollection.EncodesDemand label) xs ds)
    {heap : NaturalHeap} {cap scalar context input fuelRoot d : ℕ} (fuel : Bits)
    (capRep : StoredList heap cap capacity.toList) (deltaRep : Stored heap scalar delta)
    (inputRep : PackingStart.Input heap input label adjacency capacity xs)
    (contextRep : heap[context]?=some (.pair input fuelRoot)) (fuelRep : BoolList heap fuelRoot fuel)
    (next : ℕ) (dense : next=heap.length) (source : Bits)
    (B : ℕ) (hB : 1≤B) (labels : ∀ i,(label i).length≤B)
    (caps : ∀ x∈capacity.toList,StoredBounded x B) (scalarWidth : StoredBounded delta B)
    (saved : Registers ℕ) (pc : Fin 8340) (stack : List (Frame ℕ 8340)) :
    ∃ k ext root,
      NaturalRun program (k+1)
        (state heap next cap scalar context d (⟨pc,.r3,saved⟩::stack) source 8300) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      PackingStart.StateRecord (heap++ext) root label
        (BinaryFractionalCore.run capacity delta (BinaryFractionalGraphOracle.oracle adjacency ds capacity hn) fuel).state ∧
      k ≤ PackingRun.instructionBound ds.length n B (value fuel) fuel.length := by
  obtain ⟨k,ext,first,root,run,rep,bound⟩ := PackingRun.full_run adjacency capacity delta label numeric hn encoded
    fuel capRep deltaRep inputRep contextRep fuelRep next dense source B hB labels caps scalarWidth
  have terminal : PackingRun.program 7945=.halt := rfl
  have lifted := child_return runLabel PackingRun.program run_slots run rfl rfl
    .r3 .r3 saved pc stack (run_halt 7945 terminal)
  have entry : runLabel 7940=(8300 : Fin 8340) := rfl
  exact ⟨k,ext,root,by simpa only [PackingRun.state,entry,state,Registers.set,Registers.get] using lifted,rep,bound⟩
end DirectedFlowCutGap.PackingComplete
