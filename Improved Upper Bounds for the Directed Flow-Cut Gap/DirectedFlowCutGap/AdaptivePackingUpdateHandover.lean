import DirectedFlowCutGap.AdaptivePackingStateOutput

namespace DirectedFlowCutGap.AdaptivePackingState
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

theorem prepare_total {heap : NaturalHeap} {frame total amount : ℕ}
    (tp : HeapPath heap frame [true,true,true,true,true,true,false,true,true,true,false] total)
    (ap : HeapPath heap frame [true,true,true,false] amount)
    (next weights b ctx : ℕ) (dense : next=heap.length)
    (stack : List (Frame ℕ 4800)) (source : Bits) :
    ∃ ext,ext.length=1 ∧ NaturalRun program 18
      (state heap next weights b ctx frame stack source 4501) []
      (state (heap++ext) (next+1) total amount next frame stack source 4519) ∧
      (heap++ext)[next]?=some (.pair weights frame) := by
  let ext : NaturalHeap := [.pair weights frame]
  have pair : (heap++ext)[next]?=some (.pair weights frame) := by simp [ext,dense]
  have make : tickNatural program (state heap next weights b ctx frame stack source 4501)=
      some ⟨state (heap++ext) (next+1) weights b next frame stack source 4502,[],0⟩ := by
    have slot : program 4501=.make .r2 (.pair .r0 .r3) 4502 := rfl
    simp [tickNatural,state,slot,Registers.get,Registers.set,allocateNatural,Recipe.cell,ext]
  have p₁ : HeapPath (heap++ext) next [true,true,true,true,true,true,true,false,true,true,true,false] total :=
    .cons pair (path_extend tp ext)
  have p₂ : HeapPath (heap++ext) next [true,true,true,true,false] amount := .cons pair (path_extend ap ext)
  have s₁ : FieldSequence .r0 .r2 4502 [true,true,true,true,true,true,true,false,true,true,true,false] 4514 := .cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.nil _))))))))))))
  have s₂ : FieldSequence .r1 .r2 4514 [true,true,true,true,false] 4519 := .cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.nil _)))))
  have r₁ := field_sequence_run (regs:=⟨weights,b,next,frame⟩) s₁ p₁ (next+1) stack source
  have r₂ := field_sequence_run (regs:=⟨total,b,next,frame⟩) s₂ p₂ (next+1) stack source
  refine ⟨ext,rfl,?_,pair⟩
  simpa [state,Registers.get,Registers.set] using NaturalRun.step make (run_append r₁ r₂)

theorem prepare_loads {heap : NaturalHeap} {frame mask amount loads : ℕ}
    (mp : HeapPath heap frame [true,true,true,true,true,false,false] mask)
    (ap : HeapPath heap frame [true,true,true,true,false] amount)
    (lp : HeapPath heap frame [true,true,true,true,true,true,true,false,true,true,true,true,false] loads)
    (next a b total : ℕ) (dense : next=heap.length)
    (stack : List (Frame ℕ 4800)) (source : Bits) :
    ∃ ext,ext.length=2 ∧ NaturalRun program 30
      (state heap next a b frame total stack source 4520) []
      (state (heap++ext) (next+2) loads (next+1) next total stack source 4550) ∧
      (heap++ext)[next]?=some (.pair total frame) ∧
      (heap++ext)[next+1]?=some (.pair mask amount) := by
  let e₁ : NaturalHeap := [.pair total frame]
  let h₁ := heap++e₁
  let e₂ : NaturalHeap := [.pair mask amount]
  let h₂ := h₁++e₂
  have pair : h₁[next]?=some (.pair total frame) := by simp [h₁,e₁,dense]
  have make : tickNatural program (state heap next a b frame total stack source 4520)=
      some ⟨state h₁ (next+1) a b next total stack source 4521,[],0⟩ := by
    have slot : program 4520=.make .r2 (.pair .r3 .r2) 4521 := rfl
    simp [tickNatural,state,slot,Registers.get,Registers.set,allocateNatural,Recipe.cell,h₁,e₁]
  have p₁ : HeapPath h₁ next [true,true,true,true,true,true,false,false] mask := .cons pair (path_extend mp e₁)
  have p₂ : HeapPath h₁ next [true,true,true,true,true,false] amount := .cons pair (path_extend ap e₁)
  have s₁ : FieldSequence .r0 .r2 4521 [true,true,true,true,true,true,false,false] 4529 := .cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.nil _))))))))
  have s₂ : FieldSequence .r1 .r2 4529 [true,true,true,true,true,false] 4535 := .cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.nil _))))))
  have r₁ := field_sequence_run (regs:=⟨a,b,next,total⟩) s₁ p₁ (next+1) stack source
  have r₂ := field_sequence_run (regs:=⟨mask,b,next,total⟩) s₂ p₂ (next+1) stack source
  have context : tickNatural program (state h₁ (next+1) mask amount next total stack source 4535)=
      some ⟨state h₂ (next+2) mask (next+1) next total stack source 4536,[],0⟩ := by
    have slot : program 4535=.make .r1 (.pair .r0 .r1) 4536 := rfl
    simp [tickNatural,state,slot,Registers.get,Registers.set,allocateNatural,Recipe.cell,h₂,e₂,Nat.add_assoc]
  have p₃ : HeapPath h₂ next [true,true,true,true,true,true,true,true,false,true,true,true,true,false] loads :=
    .cons (lookup_extend pair e₂) (path_extend (path_extend lp e₁) e₂)
  have s₃ : FieldSequence .r0 .r2 4536 [true,true,true,true,true,true,true,true,false,true,true,true,true,false] 4550 := .cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.nil _))))))))))))))
  have r₃ := field_sequence_run (regs:=⟨mask,next+1,next,total⟩) s₃ p₃ (next+2) stack source
  refine ⟨e₁++e₂,rfl,?_,?_,?_⟩
  · simpa [state,Registers.get,Registers.set,h₂,h₁,List.append_assoc] using
      NaturalRun.step make (run_append r₁ (run_append r₂ (.step context r₃)))
  · simpa [h₁,List.append_assoc] using lookup_extend pair e₂
  · simp [e₁,e₂,dense]
end DirectedFlowCutGap.AdaptivePackingState
