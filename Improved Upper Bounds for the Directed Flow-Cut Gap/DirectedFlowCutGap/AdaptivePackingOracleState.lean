import DirectedFlowCutGap.AdaptivePackingContextState

namespace DirectedFlowCutGap.AdaptivePackingState
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

theorem prepare_oracle {heap : NaturalHeap} {base cap original input demands metadata : ℕ}
    (frame : BaseFrame heap base cap original input)
    (data : heap[input]?=some (.pair demands metadata))
    (next a b context : ℕ) (stack : List (Frame ℕ 4800)) (source : Bits) :
    NaturalRun program 4 (state heap next a b base context stack source 4411) []
      (state heap next demands context base context stack source 4415) := by
  obtain ⟨tail,h₁,h₂⟩ := frame
  have path : HeapPath heap base [true,true,false] demands :=
    .cons h₁ (.cons h₂ (.cons data (.nil _)))
  have slots : FieldSequence .r0 .r2 4412 [true,true,false] 4415 :=
    .cons rfl (.cons rfl (.cons rfl (.nil _)))
  have run := field_sequence_run (regs:=⟨a,context,base,context⟩) slots path next stack source
  have move : tickNatural program (state heap next a b base context stack source 4411)=
      some ⟨state heap next a context base context stack source 4412,[],0⟩ := by
    have slot : program 4411=.move .r1 .r3 4412 := rfl
    simp [tickNatural,state,slot,Registers.get,Registers.set]
  simpa [state,Registers.get,Registers.set] using NaturalRun.step move run

theorem constructed_context {n : ℕ} (label : Fin n → Bits)
    (adjacency : BinaryFractionalWalkOracle.Adjacency n) (capacity y : Row n)
    {heap : NaturalHeap} {a b input d weights k demands metadata : ℕ}
    (current : heap[b]?=some (.pair weights k))
    (data : heap[input]?=some (.pair demands metadata))
    (row : StoredList heap weights y.toList)
    (metadataRep : PackingGraphContext.Static heap metadata label adjacency capacity)
    (next : ℕ) (dense : next=heap.length) (stack : List (Frame ℕ 4800)) (source : Bits) :
    ∃ ext context,ext.length=5 ∧ NaturalRun program 23
      (state heap next a b input d stack source 4402) []
      (state (heap++ext) (next+ext.length) demands context (next+1) context stack source 4415) ∧
      BaseFrame (heap++ext) (next+1) a b input ∧
      GraphOracleMachine.Context (heap++ext) context label adjacency capacity y := by
  obtain ⟨e₁,l₁,r₁,base⟩ := prepare_context current data next dense stack source
  obtain ⟨e₂,context,l₂,r₂,rep⟩ := context_return label adjacency capacity y
    (list_extend row e₁) (PackingStart.static_extend metadataRep e₁) (next+2) (next+1) d
    (by simp [List.length_append,←dense,l₁]) ⟨weights,metadata,next+1,d⟩ 4411 stack source
  have call : tickNatural program
      (state (heap++e₁) (next+2) weights metadata (next+1) d stack source 4410)=
      some ⟨state (heap++e₁) (next+2) weights metadata (next+1) d
        (⟨4411,.r3,⟨weights,metadata,next+1,d⟩⟩::stack) source 492,[],0⟩ := by
    have slot : program 4410=.call 492 4411 .r3 := rfl
    simp [tickNatural,state,slot]
  have handover := prepare_oracle (base_extend base e₂)
    (lookup_extend (lookup_extend data e₁) e₂) (next+2+e₂.length) weights metadata context stack source
  refine ⟨e₁++e₂,context,by simp [l₁,l₂],?_,?_,?_⟩
  · simpa [List.append_assoc,List.length_append,l₁,Nat.add_assoc] using
      run_append r₁ (NaturalRun.step call (run_append r₂ handover))
  · simpa [List.append_assoc] using base_extend base e₂
  · simpa [List.append_assoc] using rep
end DirectedFlowCutGap.AdaptivePackingState
