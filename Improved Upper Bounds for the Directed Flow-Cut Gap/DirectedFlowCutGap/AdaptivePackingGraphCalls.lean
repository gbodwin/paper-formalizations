import DirectedFlowCutGap.AdaptivePackingArithmeticCalls

namespace DirectedFlowCutGap.AdaptivePackingState
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

theorem context_return {n : ℕ} (label : Fin n → Bits)
    (adjacency : BinaryFractionalWalkOracle.Adjacency n) (capacity y : Row n)
    {heap : NaturalHeap} {a b : ℕ} (weights : StoredList heap a y.toList)
    (metadata : PackingGraphContext.Static heap b label adjacency capacity) (next c d : ℕ)
    (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 4800)
    (stack : List (Frame ℕ 4800)) (source : Bits) :
    ∃ ext root,ext.length=3 ∧ NaturalRun program 10
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 492) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      GraphOracleMachine.Context (heap++ext) root label adjacency capacity y := by
  obtain ⟨ext,root,len,run,rep⟩ := PackingGraphContext.construct_return label adjacency capacity y
    weights metadata next c d hn ⟨a,b,c,d⟩ 9 [] source
  have ht : tickNatural PackingGraphContext.program (PackingGraphContext.state heap next a b c d [] source 8)=
      some ⟨PackingGraphContext.state heap next a b c d [⟨9,.r3,⟨a,b,c,d⟩⟩] source 0,[],0⟩ := by
    simp [tickNatural,PackingGraphContext.program,PackingGraphContext.state]
  have lifted := call_run contextLabel PackingGraphContext.program context_slots (.step ht run)
    (by simp [program,contextLabel,PackingGraphContext.program,callable]) saved pc stack
  refine ⟨ext,root,len,?_,rep⟩
  simpa [state,PackingGraphContext.state,contextLabel] using lifted

theorem oracle_return {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (capacity y : Row n) (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val) (hn : 0<n)
    {xs : List DemandCollection.Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (DemandCollection.EncodesDemand label) xs ds)
    {heap : NaturalHeap} {a b : ℕ} (input : DemandCollection.DemandList heap a xs)
    (context : GraphOracleMachine.Context heap b label adjacency capacity y)
    (next c d : ℕ) (dense : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 4800) (stack : List (Frame ℕ 4800)) (source : Bits) :
    ∃ steps ext root,NaturalRun program steps
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 2594) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      OracleChoice.StoredChoice (heap++ext) root label
        (BinaryFractionalGraphOracle.oracle adjacency ds capacity hn y).1 ∧
      ∀ W,1≤W → (∀ i,(label i).length≤W) → (∀ q∈y.toList,StoredBounded q W) →
        (∀ i,(get capacity i).num.length≤W ∧ (get capacity i).den.length≤W) →
        steps ≤ GraphOracleMachine.instructionBound ds.length n W+1 := by
  obtain ⟨t,ext,_,_,root,high,rep,bound⟩ := GraphOracleMachine.oracle_run adjacency capacity y label hlabel hn
    encoded input context next c d dense [] source
  have run := call_run oracleLabel GraphOracleMachine.program oracle_slots high
    (by simp [program,oracleLabel,GraphOracleMachine.program,callable]) saved pc stack
  refine ⟨t+1,ext,root,?_,rep,?_⟩
  · simpa [state,GraphOracleMachine.state,oracleLabel] using run
  · intro W hW labels rows capacities
    have hb := bound W labels capacities
    have hd := DemandCollection.graph_steps_bound adjacency y label hlabel encoded (next+1) W hW labels rows
    have hp := GraphOracleMachine.post_steps_bound adjacency y ds rows
    rw [encoded.length_eq] at hd
    unfold GraphOracleMachine.instructionBound
    omega
end DirectedFlowCutGap.AdaptivePackingState
