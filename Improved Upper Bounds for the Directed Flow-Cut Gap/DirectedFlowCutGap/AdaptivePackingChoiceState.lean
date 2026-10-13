import DirectedFlowCutGap.AdaptivePackingOracleState
import DirectedFlowCutGap.AdaptivePackingScalarCalls

namespace DirectedFlowCutGap.AdaptivePackingState
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

def ChoiceFrame (heap : NaturalHeap) (root choice cap original input : ℕ) : Prop :=
  ∃ base,heap[root]?=some (.pair choice base) ∧ BaseFrame heap base cap original input

theorem choice_frame_extend {heap : NaturalHeap} {root choice cap original input : ℕ}
    (h : ChoiceFrame heap root choice cap original input) (ext : NaturalHeap) :
    ChoiceFrame (heap++ext) root choice cap original input := by
  obtain ⟨base,pair,frame⟩ := h
  exact ⟨base,lookup_extend pair ext,base_extend frame ext⟩

theorem choice_extend {n : ℕ} {heap : NaturalHeap} {root : ℕ} {label : Fin n → Bits}
    {q : BinaryFractionalCore.Choice n} (h : OracleChoice.StoredChoice heap root label q)
    (ext : NaturalHeap) : OracleChoice.StoredChoice (heap++ext) root label q := by
  obtain ⟨mask,index,pair,hm,hi⟩ := h
  exact ⟨mask,index,lookup_extend pair ext,boolList_extend hm ext,boolList_extend hi ext⟩

theorem prepare_amount {heap : NaturalHeap} {base cap original input : ℕ}
    (frame : BaseFrame heap base cap original input)
    (next a b choice : ℕ) (dense : next=heap.length)
    (stack : List (Frame ℕ 4800)) (source : Bits) :
    ∃ ext,ext.length=1 ∧ NaturalRun program 4
      (state heap next a b base choice stack source 4416) []
      (state (heap++ext) (next+1) choice cap next choice stack source 4420) ∧
      ChoiceFrame (heap++ext) next choice cap original input := by
  let ext : NaturalHeap := [.pair choice base]
  obtain ⟨tail,h₁,h₂⟩ := frame
  have pair : (heap++ext)[next]?=some (.pair choice base) := by simp [ext,dense]
  have basePair := lookup_extend h₁ ext
  have move : tickNatural program (state heap next a b base choice stack source 4416)=
      some ⟨state (heap++ext) (next+1) a b next choice stack source 4417,[],0⟩ := by
    have slot : program 4416=.make .r2 (.pair .r3 .r2) 4417 := rfl
    simp [tickNatural,state,slot,Registers.get,Registers.set,allocateNatural,Recipe.cell,ext]
  have p₁ : HeapPath (heap++ext) next [false] choice := .cons pair (.nil _)
  have p₂ : HeapPath (heap++ext) next [true,false] cap := .cons pair (.cons basePair (.nil _))
  have s₁ : FieldSequence .r0 .r2 4417 [false] 4418 := .cons rfl (.nil _)
  have s₂ : FieldSequence .r1 .r2 4418 [true,false] 4420 := .cons rfl (.cons rfl (.nil _))
  have r₁ := field_sequence_run (regs:=⟨a,b,next,choice⟩) s₁ p₁ (next+1) stack source
  have r₂ := field_sequence_run (regs:=⟨choice,b,next,choice⟩) s₂ p₂ (next+1) stack source
  refine ⟨ext,rfl,?_,⟨base,pair,tail,basePair,lookup_extend h₂ ext⟩⟩
  simpa [state,Registers.get,Registers.set] using NaturalRun.step move (run_append r₁ r₂)
theorem actual_choice_prefix {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (capacity y : Row n) (label : Fin n → Bits) (numeric : ∀ i,value (label i)=i.val) (hn : 0<n)
    {xs : List DemandCollection.Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (DemandCollection.EncodesDemand label) xs ds)
    {heap : NaturalHeap} {a b input d weights k demands metadata : ℕ}
    (current : heap[b]?=some (.pair weights k))
    (data : heap[input]?=some (.pair demands metadata))
    (row : StoredList heap weights y.toList)
    (metadataRep : PackingGraphContext.Static heap metadata label adjacency capacity)
    (demandRep : DemandCollection.DemandList heap demands xs)
    (next : ℕ) (dense : next=heap.length) (stack : List (Frame ℕ 4800)) (source : Bits) :
    ∃ steps ext choice frame,NaturalRun program steps
      (state heap next a b input d stack source 4402) []
      (state (heap++ext) (next+ext.length) choice a frame choice stack source 4420) ∧
      ChoiceFrame (heap++ext) frame choice a b input ∧
      OracleChoice.StoredChoice (heap++ext) choice label
        (BinaryFractionalGraphOracle.oracle adjacency ds capacity hn y).1 ∧
      ∀ W,1≤W → (∀ i,(label i).length≤W) → (∀ q∈y.toList,StoredBounded q W) →
        (∀ i,(get capacity i).num.length≤W ∧ (get capacity i).den.length≤W) →
        steps ≤ GraphOracleMachine.instructionBound ds.length n W+29 := by
  obtain ⟨e₁,context,l₁,r₁,base,rep⟩ := constructed_context (a:=a) (d:=d) label adjacency capacity y current data
    row metadataRep next dense stack source
  obtain ⟨t,e₂,choice,r₂,choiceRep,bound⟩ := oracle_return adjacency capacity y label numeric hn encoded
    (DemandCollection.demands_extend demandRep e₁) rep (next+e₁.length) (next+1) context
    (by simp [List.length_append,dense]) ⟨demands,context,next+1,context⟩ 4416 stack source
  have call : tickNatural program
      (state (heap++e₁) (next+e₁.length) demands context (next+1) context stack source 4415)=
      some ⟨state (heap++e₁) (next+e₁.length) demands context (next+1) context
        (⟨4416,.r3,⟨demands,context,next+1,context⟩⟩::stack) source 2594,[],0⟩ := by
    have slot : program 4415=.call 2594 4416 .r3 := rfl
    simp [tickNatural,state,slot]
  obtain ⟨e₃,l₃,r₃,frameRep⟩ := prepare_amount (base_extend base e₂)
    (next+e₁.length+e₂.length) demands context choice (by simp [List.length_append,dense,Nat.add_assoc]) stack source
  refine ⟨23+(1+(t+4)),e₁++e₂++e₃,choice,next+e₁.length+e₂.length,?_,?_,?_,?_⟩
  · simpa [List.append_assoc,List.length_append,l₃,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      run_append r₁ (.step call (run_append r₂ r₃))
  · simpa [List.append_assoc] using frameRep
  · simpa [List.append_assoc] using choice_extend choiceRep e₃
  · intro W hW labels rows caps
    have ht := bound W hW labels rows caps
    omega
end DirectedFlowCutGap.AdaptivePackingState
