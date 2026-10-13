import DirectedFlowCutGap.AvoidingZeroContextCallLift

namespace DirectedFlowCutGap.AvoidingZeroContext
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor
open CanonicalRationalSum (StoredList)
open RationalComparisonProgram (Stored)

theorem vertices_spine {heap : NaturalHeap} {a : ℕ} {vs : List Bits}
    (h : GraphDiscoveryProgram.Vertices heap a vs) : IndexSpine heap a vs.length := by
  induction h with
  | nil hp => exact .nil hp
  | cons hp _ _ ih => exact .cons hp ih

theorem zero_return {heap : NaturalHeap} {a : ℕ} {vs : List Bits}
    (vertices : GraphDiscoveryProgram.Vertices heap a vs)
    (next b c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 64)
    (stack : List (Frame ℕ 64)) (source : Bits) :
    ∃ ext root zr rr,ext.length=vs.length+6 ∧ NaturalRun program (5*vs.length+10)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 28) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      (heap++ext)[root]?=some (.pair zr rr) ∧
      StoredList (heap++ext) rr (List.replicate vs.length BinaryRational.zero) ∧
      Stored (heap++ext) zr BinaryRational.zero := by
  obtain ⟨ext,root,zr,rr,len,run,hp,hr,hz⟩ := PackingZeroRow.zero_packed (vertices_spine vertices) next b c d hn source
  have lifted := child_return zeroLabel PackingZeroRow.program zero_slots run rfl rfl
    .r3 .r3 saved pc stack (by rfl)
  refine ⟨ext,root,zr,rr,len,?_,hp,hr,hz⟩
  simpa [PackingZeroRow.state,zeroLabel,state,Registers.get,Registers.set,Nat.add_assoc] using lifted

theorem context_return {heap : NaturalHeap} {a b : ℕ} {vs adjacency : List Bits}
    {rows : List Fraction} {sw target : Bits}
    (vertices : GraphDiscoveryProgram.Vertices heap a vs)
    (context : AvoidingGraphContext.Input heap b adjacency rows sw target)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 64)
    (stack : List (Frame ℕ 64)) (source : Bits) :
    ∃ ext root,ext.length=5 ∧ NaturalRun program 17
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 18) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      GraphDiscoveryProgram.GlobalContext (heap++ext) root vs adjacency rows sw target := by
  obtain ⟨ext,root,len,run,rep⟩ := AvoidingGraphContext.construct vertices context next c d hn [] source
  have lifted := child_return contextLabel AvoidingGraphContext.program context_slots run rfl rfl
    .r3 .r3 saved pc stack (by rfl)
  refine ⟨ext,root,len,?_,rep⟩
  simpa [AvoidingGraphContext.state,contextLabel,state,Registers.get,Registers.set] using lifted
end DirectedFlowCutGap.AvoidingZeroContext
