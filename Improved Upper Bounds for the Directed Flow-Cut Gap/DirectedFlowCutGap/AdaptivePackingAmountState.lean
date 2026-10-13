import DirectedFlowCutGap.AdaptivePackingChoiceState

namespace DirectedFlowCutGap.AdaptivePackingState
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

def AmountFrame (heap : NaturalHeap) (root amount choice cap original input : ℕ) : Prop :=
  ∃ frame,heap[root]?=some (.pair amount frame) ∧ ChoiceFrame heap frame choice cap original input

theorem amount_frame_extend {heap : NaturalHeap} {root amount choice cap original input : ℕ}
    (h : AmountFrame heap root amount choice cap original input) (ext : NaturalHeap) :
    AmountFrame (heap++ext) root amount choice cap original input := by
  obtain ⟨frame,pair,rep⟩ := h
  exact ⟨frame,lookup_extend pair ext,choice_frame_extend rep ext⟩

theorem prepare_normalized {heap : NaturalHeap} {frame choice cap original input weights k mask index : ℕ}
    (cf : ChoiceFrame heap frame choice cap original input)
    (current : heap[original]?=some (.pair weights k))
    (q : heap[choice]?=some (.pair mask index))
    (next a b amount : ℕ) (dense : next=heap.length)
    (stack : List (Frame ℕ 4800)) (source : Bits) :
    ∃ ext,ext.length=1 ∧ NaturalRun program 9
      (state heap next a b frame amount stack source 4421) []
      (state (heap++ext) (next+1) weights mask next amount stack source 4430) ∧
      AmountFrame (heap++ext) next amount choice cap original input := by
  let ext : NaturalHeap := [.pair amount frame]
  obtain ⟨base,hc,tail,hb,ht⟩ := cf
  have pair : (heap++ext)[next]?=some (.pair amount frame) := by simp [ext,dense]
  have move : tickNatural program (state heap next a b frame amount stack source 4421)=
      some ⟨state (heap++ext) (next+1) a b next amount stack source 4422,[],0⟩ := by
    have slot : program 4421=.make .r2 (.pair .r3 .r2) 4422 := rfl
    simp [tickNatural,state,slot,Registers.get,Registers.set,allocateNatural,Recipe.cell,ext]
  have p₁ : HeapPath (heap++ext) next [true,true,true,false,false] weights :=
    .cons pair (.cons (lookup_extend hc ext) (.cons (lookup_extend hb ext)
      (.cons (lookup_extend ht ext) (.cons (lookup_extend current ext) (.nil _)))))
  have p₂ : HeapPath (heap++ext) next [true,false,false] mask :=
    .cons pair (.cons (lookup_extend hc ext) (.cons (lookup_extend q ext) (.nil _)))
  have s₁ : FieldSequence .r0 .r2 4422 [true,true,true,false,false] 4427 :=
    .cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.nil _)))))
  have s₂ : FieldSequence .r1 .r2 4427 [true,false,false] 4430 :=
    .cons rfl (.cons rfl (.cons rfl (.nil _)))
  have r₁ := field_sequence_run (regs:=⟨a,b,next,amount⟩) s₁ p₁ (next+1) stack source
  have r₂ := field_sequence_run (regs:=⟨weights,b,next,amount⟩) s₂ p₂ (next+1) stack source
  refine ⟨ext,rfl,?_,⟨frame,pair,base,lookup_extend hc ext,tail,lookup_extend hb ext,lookup_extend ht ext⟩⟩
  simpa [state,Registers.get,Registers.set] using NaturalRun.step move (run_append r₁ r₂)

theorem actual_amount_handover {n : ℕ} (capacity : Row n) (q : BinaryFractionalCore.Choice n)
    (label : Fin n → Bits) (numeric : ∀ i,value (label i)=i.val)
    {heap : NaturalHeap} {choice cap frame original input weights k d : ℕ}
    (cf : ChoiceFrame heap frame choice cap original input)
    (current : heap[original]?=some (.pair weights k))
    (choiceRep : OracleChoice.StoredChoice heap choice label q)
    (capacities : StoredList heap cap capacity.toList)
    (next : ℕ) (dense : next=heap.length) (stack : List (Frame ℕ 4800)) (source : Bits) :
    ∃ ext mask amount,ext.length=q.bottleneck.val+3 ∧
      NaturalRun program (BinaryIndexedPairRead.steps (label q.bottleneck)+17)
        (state heap next choice cap frame d stack source 4420) []
        (state (heap++ext) (next+ext.length) weights mask (next+q.bottleneck.val+2) amount stack source 4430) ∧
      AmountFrame (heap++ext) (next+q.bottleneck.val+2) amount choice cap original input ∧
      Stored (heap++ext) amount (get capacity q.bottleneck) ∧
      BoolList (heap++ext) mask q.mask.toList := by
  have choiceCopy := choiceRep
  obtain ⟨mask,index,hq,hm,_⟩ := choiceRep
  obtain ⟨e₁,amount,l₁,r₁,rep⟩ := amount_return capacity q label numeric choiceCopy capacities next frame d dense
    ⟨choice,cap,frame,d⟩ 4421 stack source
  have call : tickNatural program (state heap next choice cap frame d stack source 4420)=
      some ⟨state heap next choice cap frame d (⟨4421,.r3,⟨choice,cap,frame,d⟩⟩::stack) source 2654,[],0⟩ := by
    have slot : program 4420=.call 2654 4421 .r3 := rfl
    simp [tickNatural,state,slot]
  obtain ⟨e₂,l₂,r₂,af⟩ := prepare_normalized (choice_frame_extend cf e₁)
    (lookup_extend current e₁) (lookup_extend hq e₁) (next+e₁.length) choice cap amount
    (by simp [List.length_append,dense]) stack source
  refine ⟨e₁++e₂,mask,amount,by simp [l₁,l₂,Nat.add_assoc],?_,?_,?_,?_⟩
  · convert NaturalRun.step call (run_append r₁ r₂) using 1 <;>
      simp [List.append_assoc,List.length_append,l₁,l₂,Nat.add_assoc]
  · simpa [List.append_assoc,l₁,Nat.add_assoc] using af
  · simpa [List.append_assoc] using stored_extend rep e₂
  · exact boolList_extend hm (e₁++e₂)
end DirectedFlowCutGap.AdaptivePackingState
