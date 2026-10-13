import DirectedFlowCutGap.OriginalDispatchActive

namespace DirectedFlowCutGap.OriginalDispatch
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor

theorem dispatch_return {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n) (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (ds : List (Fin n × Fin n)) {heap : NaturalHeap} {a b : ℕ}
    (table : Table heap a (ds.map fun e => (label e.1,label e.2)))
    (context : Context heap b (List.ofFn label) (IndexedRationalRead.fields costs.toList)
      (GraphRelaxationRefinement.matrix adjacency))
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 2140)
    (stack : List (Frame ℕ 2140)) (source : Bits) :
    ∃ ext out,ext.length=cells (List.ofFn label) (IndexedRationalRead.fields costs.toList)
      (GraphRelaxationRefinement.matrix adjacency) (ds.map fun e => (label e.1,label e.2)) ∧
      NaturalRun program (steps (List.ofFn label) (IndexedRationalRead.fields costs.toList)
        (GraphRelaxationRefinement.matrix adjacency) (ds.map fun e => (label e.1,label e.2)))
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 2110) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c out stack source pc) ∧
      Result (heap++ext) out (result (List.ofFn label) (IndexedRationalRead.fields costs.toList)
        (GraphRelaxationRefinement.matrix adjacency) (ds.map fun e => (label e.1,label e.2))) := by
  let frames : List (Frame ℕ 2140) := ⟨pc,.r3,saved⟩::stack
  obtain ⟨e1,ar,out,l1,start,rep,scratch⟩ := empty_prefix table context
    (original_valid adjacency label hlabel ds) next c d hn frames source
  let h1 := heap++e1
  let n1 := next+e1.length
  have hn1 : n1=h1.length := by simp [h1,n1,hn]
  cases he : EmptyDemandScan.result (GraphRelaxationRefinement.matrix adjacency)
      (ds.map fun e => (label e.1,label e.2)) with
  | some e =>
    have demand : EmptyDemandEdge.Demand h1 out e.1 e.2 := by rw [he] at rep;exact rep
    obtain ⟨sr,tr,hp,hs,ht⟩ := demand
    have branch : tickNatural program (state h1 n1 a ar next out frames source 2114)=
        some ⟨state h1 n1 a ar next out frames source 2115,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,tagBranch,hp]
    have finish := tag_return (some false) h1 n1 a ar next out saved pc stack source
    have whole := run_append start (.step branch finish)
    let extra : NaturalHeap := [tagCell (some false),.pair n1 out]
    refine ⟨e1++extra,n1+1,?_,?_,?_⟩
    · simp [cells,he,extra,l1]
    · convert whole using 1 <;> simp [steps,he,extra,state,h1,n1,List.append_assoc,Nat.add_assoc]
    · simp only [result,he,Result]
      refine ⟨n1,out,?_,?_,?_⟩
      · have h : (h1++extra)[n1+1]?=some (.pair n1 out) := by simp [extra,hn1]
        simpa only [h1,List.append_assoc] using h
      · have h : (h1++extra)[n1]?=some (.flag false) := by simp [extra,hn1,tagCell]
        simpa only [h1,List.append_assoc] using h
      · simpa only [h1,List.append_assoc] using EmptyDemandEdge.demand_extend ⟨sr,tr,hp,hs,ht⟩ extra
  | none =>
    have hnil : h1[out]?=some .nil := by rw [he] at rep;exact rep
    obtain ⟨e2,root,l2,active,returned⟩ := active_return adjacency costs label hlabel ds
      (BinaryIndexedPairRead.table_extend table e1) (AvoidingDemandScan.context_extend context e1)
      scratch n1 ar out hn1 saved pc stack source
    have branch : tickNatural program (state h1 n1 a ar next out frames source 2114)=
        some ⟨state h1 n1 a ar next out frames source 2120,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,tagBranch,hnil]
    have whole := run_append start (.step branch active)
    refine ⟨e1++e2,root,?_,?_,?_⟩
    · cases hw : AvoidingDemandScan.result (List.ofFn label) (IndexedRationalRead.fields costs.toList)
        (GraphRelaxationRefinement.matrix adjacency) (ds.map fun e => (label e.1,label e.2)) <;>
        simp [cells,he,activeCells,hw,List.length_append,l1,l2,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
      all_goals simp only [←Nat.add_assoc]
    · cases hw : AvoidingDemandScan.result (List.ofFn label) (IndexedRationalRead.fields costs.toList)
        (GraphRelaxationRefinement.matrix adjacency) (ds.map fun e => (label e.1,label e.2)) <;>
        convert whole using 1 <;> simp [steps,he,activeSteps,hw,state,n1,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
      all_goals simp only [←Nat.add_assoc]
    · cases hw : AvoidingDemandScan.result (List.ofFn label) (IndexedRationalRead.fields costs.toList)
        (GraphRelaxationRefinement.matrix adjacency) (ds.map fun e => (label e.1,label e.2)) <;>
        simpa only [result,he,activeResult,hw,List.append_assoc] using returned
end DirectedFlowCutGap.OriginalDispatch
