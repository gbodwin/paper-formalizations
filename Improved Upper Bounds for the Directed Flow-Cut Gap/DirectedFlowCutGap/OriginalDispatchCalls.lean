import DirectedFlowCutGap.OriginalDispatchCallLift

namespace DirectedFlowCutGap.OriginalDispatch
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor
open IntegralNetworkFlow IntegralNetworkFlow.Tabulated

theorem empty_return {heap : NaturalHeap} {a b : ℕ} {ds : List (Bits × Bits)} {rows : List Bits}
    (table : Table heap a ds) (hm : GraphAdjacencyProgram.Matrix heap b rows)
    (valid : ∀ e∈ds,EmptyDemandScan.Valid rows e)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 2140)
    (stack : List (Frame ℕ 2140)) (source : Bits) :
    ∃ ext out,ext.length=EmptyDemandScan.cells rows ds ∧
      NaturalRun program (EmptyDemandScan.steps rows ds+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 158) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c out stack source pc) ∧
      EmptyDemandScan.Result (heap++ext) out (EmptyDemandScan.result rows ds) := by
  obtain ⟨ext,out,len,run,rep⟩ := EmptyDemandScan.scan table hm valid next c d hn [] source
  have lifted := child_return emptyLabel EmptyDemandScan.program empty_slots run rfl rfl
    .r3 .r3 saved pc stack (by rfl)
  refine ⟨ext,out,len,?_,rep⟩
  simpa [EmptyDemandScan.state,emptyLabel,state,Registers.get,Registers.set,Nat.add_assoc] using lifted

theorem zero_return {heap : NaturalHeap} {a : ℕ} {rows : List (Bits × Bits)}
    (table : Table heap a rows) (next b c d : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 2140) (stack : List (Frame ℕ 2140)) (source : Bits) :
    ∃ ext out,ext.length=2*rows.length+1 ∧
      NaturalRun program (PackingZeroMask.steps rows+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 190) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c out stack source pc) ∧
      BoolList (heap++ext) out (PackingZeroMask.mask rows) := by
  obtain ⟨ext,out,len,run,rep⟩ := PackingZeroMask.scan table next b c d hn [] source
  have lifted := child_return zeroLabel PackingZeroMask.program zero_slots run rfl rfl
    .r3 .r3 saved pc stack (by rfl)
  refine ⟨ext,out,len,?_,rep⟩
  simpa [PackingZeroMask.state,zeroLabel,state,Registers.get,Registers.set,Nat.add_assoc] using lifted

theorem scan_return {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n) (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (ds : List (Fin n × Fin n)) {heap : NaturalHeap} {a b : ℕ}
    (table : Table heap a (ds.map fun e => (label e.1,label e.2)))
    (context : Context heap b (List.ofFn label) (IndexedRationalRead.fields costs.toList)
      (GraphRelaxationRefinement.matrix adjacency))
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 2140)
    (stack : List (Frame ℕ 2140)) (source : Bits) :
    ∃ ext out,ext.length=AvoidingDemandScan.cells (List.ofFn label) (IndexedRationalRead.fields costs.toList)
      (GraphRelaxationRefinement.matrix adjacency) (ds.map fun e => (label e.1,label e.2)) ∧
      NaturalRun program (AvoidingDemandScan.steps (List.ofFn label) (IndexedRationalRead.fields costs.toList)
        (GraphRelaxationRefinement.matrix adjacency) (ds.map fun e => (label e.1,label e.2))+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 2090) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c out stack source pc) ∧
      AvoidingDemandScan.Result (heap++ext) out
        (AvoidingDemandScan.result (List.ofFn label) (IndexedRationalRead.fields costs.toList)
          (GraphRelaxationRefinement.matrix adjacency) (ds.map fun e => (label e.1,label e.2))) := by
  obtain ⟨ext,out,len,run,rep⟩ := AvoidingDemandScan.scan adjacency costs label hlabel ds table context
    next c d hn [] source
  have lifted := child_return scanLabel AvoidingDemandScan.program scan_slots run rfl rfl
    .r3 .r3 saved pc stack (by rfl)
  refine ⟨ext,out,len,?_,?_⟩
  · simpa [AvoidingDemandScan.state,scanLabel,state,Registers.get,Registers.set,Nat.add_assoc] using lifted
  · simpa only [←AvoidingDemandScan.result_original adjacency costs label hlabel ds] using rep
end DirectedFlowCutGap.OriginalDispatch
