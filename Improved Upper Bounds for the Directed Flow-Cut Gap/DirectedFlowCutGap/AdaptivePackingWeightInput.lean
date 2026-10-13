import DirectedFlowCutGap.AdaptivePackingBestState
import DirectedFlowCutGap.AdaptivePackingUpdateCalls

namespace DirectedFlowCutGap.AdaptivePackingState
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

def BestFrame (heap : NaturalHeap) (root best cost saved : ℕ) : Prop :=
  ∃ pair,heap[root]?=some (.pair pair saved) ∧ heap[pair]?=some (.pair best cost)

theorem best_frame_extend {heap : NaturalHeap} {root best cost saved : ℕ}
    (h : BestFrame heap root best cost saved) (ext : NaturalHeap) :
    BestFrame (heap++ext) root best cost saved := by
  obtain ⟨pair,a,b⟩ := h
  exact ⟨pair,lookup_extend a ext,lookup_extend b ext⟩

theorem candidate_weight_paths {heap : NaturalHeap}
    {frame candidate normalized amount choice cap original input weights k mask index : ℕ}
    (cf : CandidateFrame heap frame candidate normalized amount choice cap original input)
    (current : heap[original]?=some (.pair weights k))
    (q : heap[choice]?=some (.pair mask index)) :
    HeapPath heap frame [true,true,true,false,false] mask ∧
    HeapPath heap frame [true,true,false] amount ∧
    HeapPath heap frame [true,true,true,true,false] cap ∧
    HeapPath heap frame [true,true,true,true,true,false,false] weights := by
  obtain ⟨nf,hd,af,hn,cf,ha,base,hc,tail,hb,ht⟩ := cf
  exact ⟨.cons hd (.cons hn (.cons ha (.cons hc (.cons q (.nil _))))),
    .cons hd (.cons hn (.cons ha (.nil _))),
    .cons hd (.cons hn (.cons ha (.cons hc (.cons hb (.nil _))))),
    .cons hd (.cons hn (.cons ha (.cons hc (.cons hb (.cons ht (.cons current (.nil _)))))))⟩

theorem prepare_weights {heap : NaturalHeap} {frame mask amount cap weights : ℕ}
    (pm : HeapPath heap frame [true,true,true,false,false] mask)
    (pa : HeapPath heap frame [true,true,false] amount)
    (pc : HeapPath heap frame [true,true,true,true,false] cap)
    (pw : HeapPath heap frame [true,true,true,true,true,false,false] weights)
    (next best cost flag : ℕ) (dense : next=heap.length)
    (stack : List (Frame ℕ 4800)) (source : Bits) :
    ∃ ext,ext.length=3 ∧ NaturalRun program 28
      (state heap next best cost frame flag stack source 4472) []
      (state (heap++ext) (next+3) cap weights (next+2) (next+1) stack source 4500) ∧
      BestFrame (heap++ext) (next+1) best cost frame ∧
      (heap++ext)[next+2]?=some (.pair mask amount) := by
  let e₁ : NaturalHeap := [.pair best cost,.pair next frame]
  let h₁ := heap++e₁
  let e₂ : NaturalHeap := [.pair mask amount]
  let h₂ := h₁++e₂
  have first : h₁[next]?=some (.pair best cost) := by simp [h₁,e₁,dense]
  have second : h₁[next+1]?=some (.pair next frame) := by simp [h₁,e₁,dense]
  have ctx : h₂[next+2]?=some (.pair mask amount) := by simp [h₂,h₁,e₁,e₂,dense]
  have t₁ : tickNatural program (state heap next best cost frame flag stack source 4472)=
      some ⟨state (heap++[.pair best cost]) (next+1) best cost frame next stack source 4473,[],0⟩ := by
    have slot : program 4472=.make .r3 (.pair .r0 .r1) 4473 := rfl
    simp [tickNatural,state,slot,Registers.get,Registers.set,allocateNatural,Recipe.cell]
  have t₂ : tickNatural program (state (heap++[.pair best cost]) (next+1) best cost frame next stack source 4473)=
      some ⟨state h₁ (next+2) best cost (next+1) next stack source 4474,[],0⟩ := by
    have slot : program 4473=.make .r2 (.pair .r3 .r2) 4474 := rfl
    simp [tickNatural,state,slot,Registers.get,Registers.set,allocateNatural,Recipe.cell,h₁,e₁,List.append_assoc,Nat.add_assoc]
  have mp : HeapPath h₁ (next+1) [true,true,true,true,false,false] mask := .cons second (path_extend pm e₁)
  have ap : HeapPath h₁ (next+1) [true,true,true,false] amount := .cons second (path_extend pa e₁)
  have ms : FieldSequence .r0 .r2 4474 [true,true,true,true,false,false] 4480 := .cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.nil _))))))
  have ats : FieldSequence .r1 .r2 4480 [true,true,true,false] 4484 := .cons rfl (.cons rfl (.cons rfl (.cons rfl (.nil _))))
  have r₁ := field_sequence_run (regs:=⟨best,cost,next+1,next⟩) ms mp (next+2) stack source
  have r₂ := field_sequence_run (regs:=⟨mask,cost,next+1,next⟩) ats ap (next+2) stack source
  have save : tickNatural program (state h₁ (next+2) mask amount (next+1) next stack source 4484)=
      some ⟨state h₁ (next+2) mask amount (next+1) (next+1) stack source 4485,[],0⟩ := by
    have slot : program 4484=.move .r3 .r2 4485 := rfl
    simp [tickNatural,state,slot,Registers.get,Registers.set]
  have make : tickNatural program (state h₁ (next+2) mask amount (next+1) (next+1) stack source 4485)=
      some ⟨state h₂ (next+3) mask amount (next+2) (next+1) stack source 4486,[],0⟩ := by
    have slot : program 4485=.make .r2 (.pair .r0 .r1) 4486 := rfl
    simp [tickNatural,state,slot,Registers.get,Registers.set,allocateNatural,Recipe.cell,h₂,e₂,Nat.add_assoc]
  have cp : HeapPath h₂ (next+1) [true,true,true,true,true,false] cap :=
    .cons (lookup_extend second e₂) (path_extend (path_extend pc e₁) e₂)
  have wp : HeapPath h₂ (next+1) [true,true,true,true,true,true,false,false] weights :=
    .cons (lookup_extend second e₂) (path_extend (path_extend pw e₁) e₂)
  have cs : FieldSequence .r0 .r3 4486 [true,true,true,true,true,false] 4492 := .cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.nil _))))))
  have ws : FieldSequence .r1 .r3 4492 [true,true,true,true,true,true,false,false] 4500 := .cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.nil _))))))))
  have r₃ := field_sequence_run (regs:=⟨mask,amount,next+2,next+1⟩) cs cp (next+3) stack source
  have r₄ := field_sequence_run (regs:=⟨cap,amount,next+2,next+1⟩) ws wp (next+3) stack source
  refine ⟨e₁++e₂,rfl,?_,?_,?_⟩
  · simpa [state,Registers.get,Registers.set,h₂,h₁,List.append_assoc] using
      NaturalRun.step t₁ (.step t₂ (run_append r₁ (run_append r₂
        (.step save (.step make (run_append r₃ r₄))))))
  · exact ⟨next,by simpa [h₁,List.append_assoc] using lookup_extend second e₂,
      by simpa [h₁,List.append_assoc] using lookup_extend first e₂⟩
  · simpa [h₂,h₁,List.append_assoc] using ctx
end DirectedFlowCutGap.AdaptivePackingState
