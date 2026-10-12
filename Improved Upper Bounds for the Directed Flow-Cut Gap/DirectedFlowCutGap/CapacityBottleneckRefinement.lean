import DirectedFlowCutGap.CapacityBottleneckEncoding

namespace DirectedFlowCutGap.CapacityBottleneck
open BinaryArithmetic BinaryRational BinaryFractionalRows ImmutableReferenceSimulation BooleanTableRead
open PackedBooleanConstructor RationalComparisonProgram

def GraphContext {n : ℕ} (heap : NaturalHeap) (context : ℕ) (label : Fin n → Bits) (capacity : Row n) : Prop :=
  ∃ v t,heap[context]?=some (.pair v t) ∧
    GraphDiscoveryProgram.Vertices heap v ((List.finRange n).map label) ∧
    WordPairTableRead.Table heap t ((List.finRange n).map fun i => ((get capacity i).num,(get capacity i).den))
def Output {n : ℕ} (heap : NaturalHeap) (root : ℕ) (label : Fin n → Bits) (capacity : Row n) : Option (Fin n) → Prop
  | none => heap[root]?=some .nil
  | some i => ∃ score word,heap[root]?=some (.pair score word) ∧
      Stored heap score (get capacity i) ∧ BoolList heap word (label i)

theorem indices_flags {n : ℕ} (mask : Vector Bool n) (is : List (Fin n)) :
    (BinaryFractionalGraphOracle.indices mask is).1=is.filter (fun i => mask[i.val]) := by
  induction is with
  | nil => rfl
  | cons i is ih => cases h : mask[i.val] <;> simp [BinaryFractionalGraphOracle.indices,ih,h]

theorem output_of_related {n : ℕ} {heap : NaturalHeap} {root : ℕ} (label : Fin n → Bits) (capacity : Row n)
    {a : Option RetainedArgminProgram.Item} {b : Option (Fin n)}
    (hs : RetainedArgminProgram.Selected heap root a)
    (he : DemandCollection.OptionRelated (EncodesItem heap label capacity) a b) :
    Output heap root label capacity b := by
  cases a with
  | none =>
    cases b with
    | none => exact hs
    | some i => exact False.elim he
  | some x =>
    cases b with
    | none => exact False.elim he
    | some i =>
      obtain ⟨_,score,hp,hscore⟩ := hs
      exact ⟨score,x.payload,hp,by rw [←he.1];exact hscore,he.2⟩

theorem graph_high {n : ℕ} (label : Fin n → Bits) (capacity : Row n) (mask : Vector Bool n)
    (initial : NaturalState 244) (pc0 : initial.pc=240)
    (hn : initial.next=initial.heap.length) (empty : initial.stack=[])
    (flags : BoolList initial.heap initial.registers.a ((List.finRange n).map fun i => mask[i.val]))
    (context : GraphContext initial.heap initial.registers.b label capacity) :
    ∃ xs out,List.Forall₂ (EncodesSlot label capacity mask) xs (List.finRange n) ∧
      NaturalRun program (selectedSteps initial.next xs) initial [] out ∧
      Output out.heap out.registers.d label capacity (BinaryFractionalGraphOracle.bottleneck capacity mask).1 ∧
      out.source=initial.source ∧ out.stack=[] ∧
      (∃ ext,out.heap=initial.heap++ext ∧ ext.length=selectedCells initial.next xs) ∧
      program out.pc=.halt := by
  obtain ⟨v,t,hp,hv,ht⟩ := context
  obtain ⟨xs,parallel,encoded⟩ := parallel_of_lists label capacity mask flags hv ht
  obtain ⟨out,run,selected,_,preserved,source,stack,_,ext,halt⟩ :=
    selected_high initial pc0 hn empty ⟨v,t,hp,parallel⟩
  obtain ⟨v',t',_,parallel'⟩ := preserved
  have related := selected_encode label capacity mask parallel' encoded initial.next
  have output := output_of_related label capacity selected related
  refine ⟨xs,out,encoded,run,?_,source,stack,ext,halt⟩
  simpa only [BinaryFractionalGraphOracle.bottleneck,indices_flags] using output

end DirectedFlowCutGap.CapacityBottleneck
