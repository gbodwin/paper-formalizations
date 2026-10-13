import DirectedFlowCutGap.AvoidingShortestCallLift

namespace DirectedFlowCutGap.AvoidingShortest
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor
open GraphWalkExtension

theorem zero_return {heap : NaturalHeap} {a b : ℕ} {vs adjacency : List Bits} {sw target : Bits}
    (vertices : GraphDiscoveryProgram.Vertices heap a vs)
    (metadata : AvoidingZeroContext.Static heap b adjacency sw target)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 1440)
    (stack : List (Frame ℕ 1440)) (source : Bits) :
    ∃ ext root,ext.length=vs.length+14 ∧ NaturalRun program (5*vs.length+39)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 62) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      GraphDiscoveryProgram.GlobalContext (heap++ext) root vs adjacency
        (List.replicate vs.length BinaryRational.zero) sw target := by
  obtain ⟨ext,root,len,run,rep⟩ := AvoidingZeroContext.construct vertices metadata next c d hn [] source
  have lifted := child_return zeroLabel AvoidingZeroContext.program zero_slots run rfl rfl
    .r3 .r3 saved pc stack (by rfl)
  refine ⟨ext,root,len,?_,rep⟩
  simpa [AvoidingZeroContext.state,AvoidingZeroContext.inputSteps,zeroLabel,state,
    Registers.get,Registers.set,Nat.add_assoc] using lifted

theorem graph_return {heap : NaturalHeap} {a b c : ℕ} {vs adjacency : List Bits}
    {values : List Fraction} {sw target u : Bits} (N : ℕ)
    (input : GraphDiscoveryProgram.Vertices heap a vs)
    (context : GraphDiscoveryProgram.GlobalContext heap b vs adjacency values sw target)
    (word : BoolList heap c u) (rows : N ≤ adjacency.length)
    (cols : ∀ (i : ℕ) (hi : i<N),N ≤ (adjacency[i]'(lt_of_lt_of_le hi rows)).length)
    (hv : ∀ v∈vs,value v<N) (ht : value target<N) (hc : ∀ v∈vs,value v<values.length)
    (valid : ∀ q,GraphDiscoveryProgram.minimize vs adjacency values sw target u=some q →
      ∀ w∈(CostedSupportProgram.edges vs adjacency q.edges sw target).map Prod.fst,value w<values.length)
    (next d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 1440)
    (stack : List (Frame ℕ 1440)) (source : Bits) :
    ∃ ext root,ext.length=GraphRecoveryController.cells vs adjacency values sw target u ∧
      NaturalRun program (GraphRecoveryController.steps vs adjacency values sw target u+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 1406) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      GraphDiscoveryProgram.StoredOption (heap++ext) root (GraphRecoveryController.result vs adjacency values sw target u) := by
  obtain ⟨ext,root,len,run,rep⟩ := GraphRecoveryController.shortest_high N
    (GraphRecoveryController.state heap next a b c d [] source 1342) rfl hn rfl
    input context word rows cols hv ht hc valid
  have lifted := child_return graphLabel GraphRecoveryController.program graph_slots run rfl rfl
    .r3 .r3 saved pc stack (by rfl)
  refine ⟨ext,root,len,?_,rep⟩
  simpa [GraphRecoveryController.state,graphLabel,state,Registers.get,Registers.set,Nat.add_assoc] using lifted
end DirectedFlowCutGap.AvoidingShortest
