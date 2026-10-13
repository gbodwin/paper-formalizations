import DirectedFlowCutGap.AdaptivePackingObjectiveState

namespace DirectedFlowCutGap.AdaptivePackingState
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

theorem candidate_original_path {heap : NaturalHeap} {frame candidate normalized amount choice cap original input : ℕ}
    (cf : CandidateFrame heap frame candidate normalized amount choice cap original input) :
    HeapPath heap frame [true,true,true,true,true,false] original := by
  obtain ⟨nf,pair,rep⟩ := cf
  exact .cons pair (normalized_original_path rep)

theorem new_best_path {heap : NaturalHeap} {frame candidate normalized amount choice cap original input : ℕ}
    (cf : CandidateFrame heap frame candidate normalized amount choice cap original input)
    (next a b flag : ℕ) (stack : List (Frame ℕ 4800)) (source : Bits) :
    NaturalRun program 4 (state heap next a b frame flag stack source 4451) []
      (state heap next normalized candidate frame flag stack source 4472) := by
  obtain ⟨nf,hc,af,hn,_⟩ := cf
  have p₁ : HeapPath heap frame [true,false] normalized := .cons hc (.cons hn (.nil _))
  have p₂ : HeapPath heap frame [false] candidate := .cons hc (.nil _)
  have s₁ : FieldSequence .r0 .r2 4451 [true,false] 4453 := .cons rfl (.cons rfl (.nil _))
  have s₂ : FieldSequence .r1 .r2 4453 [false] 4454 := .cons rfl (.nil _)
  have r₁ := field_sequence_run (regs:=⟨a,b,frame,flag⟩) s₁ p₁ next stack source
  have r₂ := field_sequence_run (regs:=⟨normalized,b,frame,flag⟩) s₂ p₂ next stack source
  have move : tickNatural program (state heap next normalized candidate frame flag stack source 4454)=
      some ⟨state heap next normalized candidate frame flag stack source 4472,[],0⟩ := by
    have slot : program 4454=.move .r0 .r0 4472 := rfl
    simp [tickNatural,state,slot,Registers.get,Registers.set]
  simpa [state,Registers.get,Registers.set] using run_append r₁ (run_append r₂ (.step move (.done _)))

theorem old_best_path {heap : NaturalHeap} {frame candidate normalized amount choice cap original input best cost : ℕ}
    (cf : CandidateFrame heap frame candidate normalized amount choice cap original input)
    (bestPath : HeapPath heap original [true,false] best)
    (costPath : HeapPath heap original [true,true,false] cost)
    (next a b flag : ℕ) (stack : List (Frame ℕ 4800)) (source : Bits) :
    NaturalRun program 17 (state heap next a b frame flag stack source 4455) []
      (state heap next best cost frame flag stack source 4472) := by
  have p₁ := path_append (candidate_original_path cf) bestPath
  have p₂ := path_append (candidate_original_path cf) costPath
  have s₁ : FieldSequence .r0 .r2 4455 [true,true,true,true,true,false,true,false] 4463 :=
    .cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.nil _))))))))
  have s₂ : FieldSequence .r1 .r2 4463 [true,true,true,true,true,false,true,true,false] 4472 :=
    .cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.nil _)))))))))
  have r₁ := field_sequence_run (regs:=⟨a,b,frame,flag⟩) s₁ p₁ next stack source
  have r₂ := field_sequence_run (regs:=⟨best,b,frame,flag⟩) s₂ p₂ next stack source
  simpa [state,Registers.get,Registers.set] using run_append r₁ r₂

def selectionSteps (keep : Bool) : ℕ := if keep then 18 else 5

theorem select_best {heap : NaturalHeap} {frame candidate normalized amount choice cap original input best cost flag : ℕ}
    (cf : CandidateFrame heap frame candidate normalized amount choice cap original input)
    (bestPath : HeapPath heap original [true,false] best)
    (costPath : HeapPath heap original [true,true,false] cost)
    (keep : Bool) (bit : heap[flag]?=some (.flag keep))
    (next a b : ℕ) (stack : List (Frame ℕ 4800)) (source : Bits) :
    NaturalRun program (selectionSteps keep) (state heap next a b frame flag stack source 4450) []
      (state heap next (if keep then best else normalized) (if keep then cost else candidate)
        frame flag stack source 4472) := by
  have slot : program 4450=.branch .r3 4799 4451 4455 4799 := rfl
  cases keep
  · have tick : tickNatural program (state heap next a b frame flag stack source 4450)=
        some ⟨state heap next a b frame flag stack source 4451,[],0⟩ := by
      simp [tickNatural,state,slot,Registers.get,tagBranch,bit]
    simpa [selectionSteps] using NaturalRun.step tick (new_best_path cf next a b flag stack source)
  · have tick : tickNatural program (state heap next a b frame flag stack source 4450)=
        some ⟨state heap next a b frame flag stack source 4455,[],0⟩ := by
      simp [tickNatural,state,slot,Registers.get,tagBranch,bit]
    simpa [selectionSteps] using NaturalRun.step tick (old_best_path cf bestPath costPath next a b flag stack source)

theorem actual_best_handover (oldCost newCost : Fraction)
    {heap : NaturalHeap} {frame candidate normalized amount choice cap original input best cost d : ℕ}
    (cf : CandidateFrame heap frame candidate normalized amount choice cap original input)
    (bestPath : HeapPath heap original [true,false] best)
    (costPath : HeapPath heap original [true,true,false] cost)
    (oldRep : Stored heap cost oldCost) (newRep : Stored heap candidate newCost)
    (next : ℕ) (dense : next=heap.length) (stack : List (Frame ℕ 4800)) (source : Bits) :
    ∃ ext flag,ext.length=RationalComparisonProgram.cells oldCost newCost ∧
      NaturalRun program (RationalComparisonProgram.instructions oldCost newCost+2+
          selectionSteps (BinaryRational.le oldCost newCost).1)
        (state heap next cost candidate frame d stack source 4449) []
        (state (heap++ext) (next+ext.length)
          (if (BinaryRational.le oldCost newCost).1 then best else normalized)
          (if (BinaryRational.le oldCost newCost).1 then cost else candidate)
          frame flag stack source 4472) := by
  obtain ⟨ext,flag,len,run,bit⟩ := comparison_return oldCost newCost oldRep newRep next frame d dense
    ⟨cost,candidate,frame,d⟩ 4450 stack source
  have call : tickNatural program (state heap next cost candidate frame d stack source 4449)=
      some ⟨state heap next cost candidate frame d (⟨4450,.r3,⟨cost,candidate,frame,d⟩⟩::stack) source 3486,[],0⟩ := by
    have slot : program 4449=.call 3486 4450 .r3 := rfl
    simp [tickNatural,state,slot]
  have selection := select_best (candidate_frame_extend cf ext) (path_extend bestPath ext) (path_extend costPath ext)
    (BinaryRational.le oldCost newCost).1 bit (next+ext.length) cost candidate stack source
  refine ⟨ext,flag,len,?_⟩
  convert NaturalRun.step call (run_append run selection) using 1 <;> first | rfl | omega
end DirectedFlowCutGap.AdaptivePackingState
