import DirectedFlowCutGap.AdaptivePackingNormalizedState

namespace DirectedFlowCutGap.AdaptivePackingState
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

def CandidateFrame (heap : NaturalHeap) (root candidate normalized amount choice cap original input : ℕ) : Prop :=
  ∃ frame,heap[root]?=some (.pair candidate frame) ∧ NormalizedFrame heap frame normalized amount choice cap original input

theorem candidate_frame_extend {heap : NaturalHeap} {root candidate normalized amount choice cap original input : ℕ}
    (h : CandidateFrame heap root candidate normalized amount choice cap original input) (ext : NaturalHeap) :
    CandidateFrame (heap++ext) root candidate normalized amount choice cap original input := by
  obtain ⟨frame,pair,rep⟩ := h
  exact ⟨frame,lookup_extend pair ext,normalized_frame_extend rep ext⟩

theorem normalized_original_path {heap : NaturalHeap} {frame normalized amount choice cap original input : ℕ}
    (nf : NormalizedFrame heap frame normalized amount choice cap original input) :
    HeapPath heap frame [true,true,true,true,false] original := by
  obtain ⟨af,hn,cf,ha,base,hc,tail,hb,ht⟩ := nf
  exact .cons hn (.cons ha (.cons hc (.cons hb (.cons ht (.nil _)))))

theorem prepare_comparison {heap : NaturalHeap} {frame normalized amount choice cap original input oldCost : ℕ}
    (nf : NormalizedFrame heap frame normalized amount choice cap original input)
    (old : HeapPath heap original [true,true,false] oldCost)
    (next a b candidate : ℕ) (dense : next=heap.length)
    (stack : List (Frame ℕ 4800)) (source : Bits) :
    ∃ ext,ext.length=1 ∧ NaturalRun program 11
      (state heap next a b frame candidate stack source 4438) []
      (state (heap++ext) (next+1) oldCost candidate next candidate stack source 4449) ∧
      CandidateFrame (heap++ext) next candidate normalized amount choice cap original input := by
  let ext : NaturalHeap := [.pair candidate frame]
  have pair : (heap++ext)[next]?=some (.pair candidate frame) := by simp [ext,dense]
  have make : tickNatural program (state heap next a b frame candidate stack source 4438)=
      some ⟨state (heap++ext) (next+1) a b next candidate stack source 4439,[],0⟩ := by
    have slot : program 4438=.make .r2 (.pair .r3 .r2) 4439 := rfl
    simp [tickNatural,state,slot,Registers.get,Registers.set,allocateNatural,Recipe.cell,ext]
  have p : HeapPath (heap++ext) next [true,true,true,true,true,false,true,true,false] oldCost :=
    .cons pair (path_extend (path_append (normalized_original_path nf) old) ext)
  have slots : FieldSequence .r0 .r2 4439 [true,true,true,true,true,false,true,true,false] 4448 :=
    .cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.nil _)))))))))
  have run := field_sequence_run (regs:=⟨a,b,next,candidate⟩) slots p (next+1) stack source
  have move : tickNatural program (state (heap++ext) (next+1) oldCost b next candidate stack source 4448)=
      some ⟨state (heap++ext) (next+1) oldCost candidate next candidate stack source 4449,[],0⟩ := by
    have slot : program 4448=.move .r1 .r3 4449 := rfl
    simp [tickNatural,state,slot,Registers.get,Registers.set]
  refine ⟨ext,rfl,?_,⟨frame,pair,normalized_frame_extend nf ext⟩⟩
  simpa [state,Registers.get,Registers.set] using NaturalRun.step make (run_append run (.step move (.done _)))

theorem actual_objective_handover {xs ys : List Fraction}
    {heap : NaturalHeap} {cap normalized frame amount choice original input oldCost d : ℕ}
    (nf : NormalizedFrame heap frame normalized amount choice cap original input)
    (old : HeapPath heap original [true,true,false] oldCost)
    (left : StoredList heap cap xs) (right : StoredList heap normalized ys) (aligned : xs.length=ys.length)
    (next : ℕ) (dense : next=heap.length) (stack : List (Frame ℕ 4800)) (source : Bits) :
    ∃ ext candidate,ext.length=ObjectiveRow.cells xs ys+1 ∧
      NaturalRun program (ObjectiveRow.steps xs ys+13)
        (state heap next cap normalized frame d stack source 4437) []
        (state (heap++ext) (next+ext.length) oldCost candidate (next+ObjectiveRow.cells xs ys) candidate
          stack source 4449) ∧
      CandidateFrame (heap++ext) (next+ObjectiveRow.cells xs ys) candidate normalized amount choice cap original input ∧
      Stored (heap++ext) candidate (ObjectiveRow.result xs ys) := by
  obtain ⟨e₁,candidate,l₁,r₁,rep⟩ := objective_return left right aligned next frame d dense
    ⟨cap,normalized,frame,d⟩ 4438 stack source
  have call : tickNatural program (state heap next cap normalized frame d stack source 4437)=
      some ⟨state heap next cap normalized frame d (⟨4438,.r3,⟨cap,normalized,frame,d⟩⟩::stack) source 3338,[],0⟩ := by
    have slot : program 4437=.call 3338 4438 .r3 := rfl
    simp [tickNatural,state,slot]
  obtain ⟨e₂,l₂,r₂,cf⟩ := prepare_comparison (normalized_frame_extend nf e₁) (path_extend old e₁)
    (next+e₁.length) cap normalized candidate (by simp [List.length_append,dense]) stack source
  refine ⟨e₁++e₂,candidate,by simp [l₁,l₂],?_,?_,?_⟩
  · convert NaturalRun.step call (run_append r₁ r₂) using 1 <;>
      simp [List.append_assoc,List.length_append,l₁,l₂,Nat.add_assoc]
  · simpa [List.append_assoc,l₁] using cf
  · simpa [List.append_assoc] using stored_extend rep e₂
end DirectedFlowCutGap.AdaptivePackingState
