import DirectedFlowCutGap.AdaptivePackingGraphCalls
import DirectedFlowCutGap.AdaptivePackingFieldPath

namespace DirectedFlowCutGap.AdaptivePackingState
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

/-- The persistent base keeps the original capacity, state and input roots. -/
def BaseFrame (heap : NaturalHeap) (root cap original input : ℕ) : Prop :=
  ∃ tail,heap[root]?=some (.pair cap tail) ∧ heap[tail]?=some (.pair original input)

theorem base_extend {heap : NaturalHeap} {root cap original input : ℕ}
    (h : BaseFrame heap root cap original input) (ext : NaturalHeap) :
    BaseFrame (heap++ext) root cap original input := by
  obtain ⟨tail,h₁,h₂⟩ := h
  exact ⟨tail,lookup_extend h₁ ext,lookup_extend h₂ ext⟩

theorem prepare_context {heap : NaturalHeap} {a b input d weights k demands metadata : ℕ}
    (current : heap[b]?=some (.pair weights k))
    (data : heap[input]?=some (.pair demands metadata))
    (next : ℕ) (dense : next=heap.length) (stack : List (Frame ℕ 4800)) (source : Bits) :
    ∃ ext,ext.length=2 ∧ NaturalRun program 8
      (state heap next a b input d stack source 4402) []
      (state (heap++ext) (next+2) weights metadata (next+1) d stack source 4410) ∧
      BaseFrame (heap++ext) (next+1) a b input := by
  let e : NaturalHeap := [.pair b input,.pair a next]
  let h1 := heap++[.pair b input]
  let h2 := heap++e
  have slot4402 : program 4402=.make .r2 (.pair .r1 .r2) 4403 := rfl
  have slot4403 : program 4403=.make .r2 (.pair .r0 .r2) 4404 := rfl
  have t4402 : tickNatural program (state heap next a b input d stack source 4402)=
      some ⟨state h1 (next+1) a b next d stack source 4403,[],0⟩ := by
    simp [tickNatural,state,slot4402,Registers.get,Registers.set,Recipe.cell,allocateNatural,h1]
  have t4403 : tickNatural program (state h1 (next+1) a b next d stack source 4403)=
      some ⟨state h2 (next+2) a b (next+1) d stack source 4404,[],0⟩ := by
    simp [tickNatural,state,slot4403,Registers.get,Registers.set,Recipe.cell,allocateNatural,h2,h1,e,List.append_assoc,Nat.add_assoc]
  have first : h2[next]?=some (.pair b input) := by simp [h2,e,dense]
  have second : h2[next+1]?=some (.pair a next) := by simp [h2,e,dense]
  have original : h2[b]?=some (.pair weights k) := lookup_extend current e
  have originalInput : h2[input]?=some (.pair demands metadata) := lookup_extend data e
  have weightPath : HeapPath h2 (next+1) [true,false,false] weights :=
    .cons second (.cons first (.cons original (.nil weights)))
  have inputPath : HeapPath h2 (next+1) [true,true,true] metadata :=
    .cons second (.cons first (.cons originalInput (.nil metadata)))
  have slotsWeight : FieldSequence .r0 .r2 4404 [true,false,false] 4407 :=
    .cons rfl (.cons rfl (.cons rfl (.nil _)))
  have slotsInput : FieldSequence .r1 .r2 4407 [true,true,true] 4410 :=
    .cons rfl (.cons rfl (.cons rfl (.nil _)))
  have w := field_sequence_run (regs:=⟨a,b,next+1,d⟩) slotsWeight weightPath (next+2) stack source
  have x := field_sequence_run (regs:=⟨weights,b,next+1,d⟩) slotsInput inputPath (next+2) stack source
  have w' : NaturalRun program 3 (state h2 (next+2) a b (next+1) d stack source 4404) []
      (state h2 (next+2) weights b (next+1) d stack source 4407) := by
    simpa [state,Registers.set,Registers.get] using w
  have x' : NaturalRun program 3 (state h2 (next+2) weights b (next+1) d stack source 4407) []
      (state h2 (next+2) weights metadata (next+1) d stack source 4410) := by
    simpa [state,Registers.set,Registers.get] using x
  refine ⟨e,rfl,?_,⟨next,second,first⟩⟩
  simpa [h2] using NaturalRun.step t4402 (.step t4403 (run_append w' x'))
end DirectedFlowCutGap.AdaptivePackingState
