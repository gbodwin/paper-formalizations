import DirectedFlowCutGap.OracleCapacityFinish

namespace DirectedFlowCutGap.OracleChoice
open BinaryArithmetic BinaryRational BinaryFractionalRows ImmutableReferenceSimulation BooleanTableRead
open PackedBooleanConstructor

/-- The mask returned by the actual constructor is passed to the literal
capacity subroutine; both selector branches retain that same mask root. -/
theorem choice_capacity_return {n : ℕ} (label : Fin n → Bits) (capacity : Row n)
    (mask : Vector Bool n) (zero : Fin n) {heap : NaturalHeap}
    {a b frame selected context maskRoot vertices table zeroRoot tail : ℕ}
    (hf : heap[frame]?=some (.pair selected context))
    (ctx : CapacityBottleneck.GraphContext heap context label capacity)
    (hc : heap[context]?=some (.pair vertices table))
    (hv : heap[vertices]?=some (.pair zeroRoot tail))
    (hz : BoolList heap zeroRoot (label zero)) (hm : BoolList heap maskRoot mask.toList)
    (next : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 484)
    (stack : List (Frame ℕ 484)) (source : Bits) :
    ∃ xs ext root,List.Forall₂ (CapacityBottleneck.EncodesSlot label capacity mask) xs (List.finRange n) ∧
      ext.length=CapacityBottleneck.selectedCells (next+1) xs+2 ∧
      NaturalRun program (CapacityBottleneck.selectedSteps (next+1) xs+
        finishSteps (BinaryFractionalGraphOracle.bottleneck capacity mask).1+5)
        (state heap next a b frame maskRoot (⟨pc,.r3,saved⟩::stack) source 421) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      StoredChoice (heap++ext) root label
        ⟨mask,(BinaryFractionalGraphOracle.bottleneck capacity mask).1.getD zero⟩ := by
  let frames := (⟨pc,.r3,saved⟩::stack)
  let extra : NaturalHeap := [.pair frame maskRoot]
  let h1 := heap++extra
  have hn1 : next+1=h1.length := by simp [h1,extra,hn]
  have flags : BoolList h1 maskRoot ((List.finRange n).map fun i => mask[i.val]) := by
    have eq : (List.finRange n).map (fun i => mask[i.val])=mask.toList := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2; simp
    rw [eq]
    exact boolList_extend hm extra
  obtain ⟨xs,ec,rc,encoded,lc,body,output⟩ := capacity_graph_return label capacity mask flags
    (graph_context_extend ctx extra) (next+1) next maskRoot hn1
    ⟨maskRoot,context,next,maskRoot⟩ 425 frames source
  have hframe : (h1++ec)[next]?=some (.pair frame maskRoot) := by
    apply lookup_extend (k:=ec)
    simp [h1,extra,hn]
  have dense : next+1+ec.length=(h1++ec).length := by simp [h1,extra,hn];omega
  obtain ⟨ef,lf,finish,stored⟩ := finish_return label capacity mask zero hframe
    (lookup_extend (lookup_extend hf extra) ec)
    (lookup_extend (lookup_extend hc extra) ec)
    (lookup_extend (lookup_extend hv extra) ec)
    (boolList_extend (boolList_extend hz extra) ec)
    (boolList_extend (boolList_extend hm extra) ec) output
    (next+1+ec.length) dense saved pc stack source
  have t421 : tickNatural program (state heap next a b frame maskRoot frames source 421)=
      some ⟨state heap next a context frame maskRoot frames source 422,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hf]
  have t422 : tickNatural program (state heap next a context frame maskRoot frames source 422)=
      some ⟨state h1 (next+1) a context next maskRoot frames source 423,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,h1,extra]
  have t423 : tickNatural program (state h1 (next+1) a context next maskRoot frames source 423)=
      some ⟨state h1 (next+1) maskRoot context next maskRoot frames source 424,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  have t424 : tickNatural program (state h1 (next+1) maskRoot context next maskRoot frames source 424)=
      some ⟨state h1 (next+1) maskRoot context next maskRoot
        (⟨425,.r3,⟨maskRoot,context,next,maskRoot⟩⟩::frames) source 400,[],0⟩ := by
    simp [tickNatural,program,state]
  let ext : NaturalHeap := extra++ec++ef
  refine ⟨xs,ext,next+1+ec.length,encoded,by simp [ext,extra,lc,lf],?_,?_⟩
  · have all := NaturalRun.step t421 (.step t422 (.step t423 (.step t424 (run_append body finish))))
    convert all using 1 <;> simp [ext,extra,h1,state,List.append_assoc,lf]
    all_goals omega
  · simpa [ext,h1,List.append_assoc] using stored

end DirectedFlowCutGap.OracleChoice
