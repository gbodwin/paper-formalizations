import DirectedFlowCutGap.OracleChoiceData

namespace DirectedFlowCutGap.OracleChoice
open BinaryArithmetic BinaryRational BinaryFractionalRows ImmutableReferenceSimulation BooleanTableRead
open PackedBooleanConstructor

/-- The actual constructed mask and original table determine the aligned input
records internally; the callable selector returns the old bottleneck result. -/
theorem capacity_graph_return {n : ℕ} (label : Fin n → Bits) (capacity : Row n) (mask : Vector Bool n)
    {heap : NaturalHeap} {a b : ℕ}
    (flags : BoolList heap a ((List.finRange n).map fun i => mask[i.val]))
    (context : CapacityBottleneck.GraphContext heap b label capacity)
    (next c d : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 484) (stack : List (Frame ℕ 484)) (source : Bits) :
    ∃ xs ext root,List.Forall₂ (CapacityBottleneck.EncodesSlot label capacity mask) xs (List.finRange n) ∧
      ext.length=CapacityBottleneck.selectedCells next xs ∧
      NaturalRun program (CapacityBottleneck.selectedSteps next xs+1)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 400) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      CapacityBottleneck.Output (heap++ext) root label capacity
        (BinaryFractionalGraphOracle.bottleneck capacity mask).1 := by
  obtain ⟨v,t,hp,hv,ht⟩ := context
  obtain ⟨xs,parallel,encoded⟩ := CapacityBottleneck.parallel_of_lists label capacity mask flags hv ht
  obtain ⟨ext,root,len,run,selected,preserved⟩ := capacity_return
    (xs:=xs) ⟨v,t,hp,parallel⟩ next c d hn saved pc stack source
  obtain ⟨v',t',_,parallel'⟩ := preserved
  have related := CapacityBottleneck.selected_encode label capacity mask parallel' encoded next
  have output := CapacityBottleneck.output_of_related label capacity selected related
  refine ⟨xs,ext,root,encoded,len,run,?_⟩
  simpa only [BinaryFractionalGraphOracle.bottleneck,CapacityBottleneck.indices_flags] using output

end DirectedFlowCutGap.OracleChoice
