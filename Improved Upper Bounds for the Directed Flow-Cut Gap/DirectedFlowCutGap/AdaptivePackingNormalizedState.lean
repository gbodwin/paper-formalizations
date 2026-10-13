import DirectedFlowCutGap.AdaptivePackingAmountState

namespace DirectedFlowCutGap.AdaptivePackingState
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

def NormalizedFrame (heap : NaturalHeap) (root normalized amount choice cap original input : ℕ) : Prop :=
  ∃ frame,heap[root]?=some (.pair normalized frame) ∧ AmountFrame heap frame amount choice cap original input

theorem normalized_frame_extend {heap : NaturalHeap} {root normalized amount choice cap original input : ℕ}
    (h : NormalizedFrame heap root normalized amount choice cap original input) (ext : NaturalHeap) :
    NormalizedFrame (heap++ext) root normalized amount choice cap original input := by
  obtain ⟨frame,pair,rep⟩ := h
  exact ⟨frame,lookup_extend pair ext,amount_frame_extend rep ext⟩

theorem prepare_objective {heap : NaturalHeap} {frame amount choice cap original input : ℕ}
    (af : AmountFrame heap frame amount choice cap original input)
    (next a b normalized : ℕ) (dense : next=heap.length)
    (stack : List (Frame ℕ 4800)) (source : Bits) :
    ∃ ext,ext.length=1 ∧ NaturalRun program 6
      (state heap next a b frame normalized stack source 4431) []
      (state (heap++ext) (next+1) cap normalized next normalized stack source 4437) ∧
      NormalizedFrame (heap++ext) next normalized amount choice cap original input := by
  let ext : NaturalHeap := [.pair normalized frame]
  obtain ⟨cf,ha,base,hc,tail,hb,ht⟩ := af
  have pair : (heap++ext)[next]?=some (.pair normalized frame) := by simp [ext,dense]
  have make : tickNatural program (state heap next a b frame normalized stack source 4431)=
      some ⟨state (heap++ext) (next+1) a b next normalized stack source 4432,[],0⟩ := by
    have slot : program 4431=.make .r2 (.pair .r3 .r2) 4432 := rfl
    simp [tickNatural,state,slot,Registers.get,Registers.set,allocateNatural,Recipe.cell,ext]
  have p : HeapPath (heap++ext) next [true,true,true,false] cap :=
    .cons pair (.cons (lookup_extend ha ext) (.cons (lookup_extend hc ext)
      (.cons (lookup_extend hb ext) (.nil _))))
  have slots : FieldSequence .r0 .r2 4432 [true,true,true,false] 4436 :=
    .cons rfl (.cons rfl (.cons rfl (.cons rfl (.nil _))))
  have run := field_sequence_run (regs:=⟨a,b,next,normalized⟩) slots p (next+1) stack source
  have move : tickNatural program (state (heap++ext) (next+1) cap b next normalized stack source 4436)=
      some ⟨state (heap++ext) (next+1) cap normalized next normalized stack source 4437,[],0⟩ := by
    have slot : program 4436=.move .r1 .r3 4437 := rfl
    simp [tickNatural,state,slot,Registers.get,Registers.set]
  refine ⟨ext,rfl,?_,⟨frame,pair,cf,lookup_extend ha ext,base,lookup_extend hc ext,
    tail,lookup_extend hb ext,lookup_extend ht ext⟩⟩
  simpa [state,Registers.get,Registers.set] using NaturalRun.step make (run_append run (.step move (.done _)))

theorem actual_normalized_handover {xs : List Fraction} {mask : List Bool}
    {heap : NaturalHeap} {weights flags frame amount choice cap original input d : ℕ}
    (af : AmountFrame heap frame amount choice cap original input)
    (row : StoredList heap weights xs) (bits : BoolList heap flags mask) (aligned : xs.length=mask.length)
    (next : ℕ) (dense : next=heap.length) (stack : List (Frame ℕ 4800)) (source : Bits) :
    ∃ ext normalized,ext.length=NormalizedRow.cells xs mask+1 ∧
      NaturalRun program (NormalizedRow.steps xs mask+8)
        (state heap next weights flags frame d stack source 4430) []
        (state (heap++ext) (next+ext.length) cap normalized (next+NormalizedRow.cells xs mask) normalized
          stack source 4437) ∧
      NormalizedFrame (heap++ext) (next+NormalizedRow.cells xs mask) normalized amount choice cap original input ∧
      StoredList (heap++ext) normalized (NormalizedRow.result xs mask) := by
  obtain ⟨e₁,normalized,l₁,r₁,rep⟩ := normalized_return row bits aligned next frame d dense
    ⟨weights,flags,frame,d⟩ 4431 stack source
  have call : tickNatural program (state heap next weights flags frame d stack source 4430)=
      some ⟨state heap next weights flags frame d (⟨4431,.r3,⟨weights,flags,frame,d⟩⟩::stack) source 3022,[],0⟩ := by
    have slot : program 4430=.call 3022 4431 .r3 := rfl
    simp [tickNatural,state,slot]
  obtain ⟨e₂,l₂,r₂,nf⟩ := prepare_objective (amount_frame_extend af e₁) (next+e₁.length) weights flags normalized
    (by simp [List.length_append,dense]) stack source
  refine ⟨e₁++e₂,normalized,by simp [l₁,l₂],?_,?_,?_⟩
  · convert NaturalRun.step call (run_append r₁ r₂) using 1 <;>
      simp [List.append_assoc,List.length_append,l₁,l₂,Nat.add_assoc]
  · simpa [List.append_assoc,l₁] using nf
  · simpa [List.append_assoc] using list_extend rep e₂
end DirectedFlowCutGap.AdaptivePackingState
