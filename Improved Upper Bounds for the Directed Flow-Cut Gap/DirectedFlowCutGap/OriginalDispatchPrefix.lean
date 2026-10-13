import DirectedFlowCutGap.OriginalDispatchTag

namespace DirectedFlowCutGap.OriginalDispatch
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor

theorem original_valid {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val) (ds : List (Fin n × Fin n)) :
    ∀ e∈ds.map (fun e => (label e.1,label e.2)),EmptyDemandScan.Valid (GraphRelaxationRefinement.matrix adjacency) e := by
  intro e he
  obtain ⟨⟨u,v⟩,_,rfl⟩ := List.mem_map.mp he
  have hi : value (label u)<(GraphRelaxationRefinement.matrix adjacency).length := by
    simpa only [hlabel,GraphRelaxationRefinement.matrix_length] using u.isLt
  refine ⟨hi,?_⟩
  simpa only [hlabel,GraphRelaxationRefinement.matrix_row_length] using v.isLt

theorem empty_prefix {heap : NaturalHeap} {a b : ℕ} {ds cs : List (Bits × Bits)} {vs rows : List Bits}
    (table : Table heap a ds) (context : Context heap b vs cs rows)
    (valid : ∀ e∈ds,EmptyDemandScan.Valid rows e)
    (next c d : ℕ) (hn : next=heap.length) (frames : List (Frame ℕ 2140)) (source : Bits) :
    ∃ ext ar out,ext.length=EmptyDemandScan.cells rows ds+1 ∧
      NaturalRun program (EmptyDemandScan.steps rows ds+6)
        (state heap next a b c d frames source 2110) []
        (state (heap++ext) (next+ext.length) a ar next out frames source 2114) ∧
      EmptyDemandScan.Result (heap++ext) out (EmptyDemandScan.result rows ds) ∧
      (heap++ext)[next]?=some (.pair a b) := by
  obtain ⟨vr,detail,cr,ar,hp,hd,hv,hc,ha⟩ := context
  let scratch : Cell ℕ := .pair a b
  let h0 : NaturalHeap := heap++[scratch]
  have hn0 : next+1=h0.length := by simp [h0,hn]
  have hp0 := lookup_extend hp [scratch]
  have hd0 := lookup_extend hd [scratch]
  obtain ⟨ex,out,len,child,rep⟩ := empty_return (BinaryIndexedPairRead.table_extend table [scratch])
    (GraphAdjacencyProgram.matrix_extend (KeptAdjacencyMatrix.matrix_to_graph ha) [scratch]) valid
    (next+1) next d hn0 ⟨a,ar,next,d⟩ 2114 frames source
  have t1 : tickNatural program (state heap next a b c d frames source 2110)=
      some ⟨state h0 (next+1) a b next d frames source 2111,[],0⟩ := by
    simp [tickNatural,program,state,h0,scratch,allocateNatural,Recipe.cell,Registers.get,Registers.set]
  have t2 : tickNatural program (state h0 (next+1) a b next d frames source 2111)=
      some ⟨state h0 (next+1) a detail next d frames source 2112,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hp0,h0]
  have t3 : tickNatural program (state h0 (next+1) a detail next d frames source 2112)=
      some ⟨state h0 (next+1) a ar next d frames source 2113,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hd0,h0]
  have t4 : tickNatural program (state h0 (next+1) a ar next d frames source 2113)=
      some ⟨state h0 (next+1) a ar next d (⟨2114,.r3,⟨a,ar,next,d⟩⟩::frames) source 158,[],0⟩ := rfl
  refine ⟨[scratch]++ex,ar,out,?_,?_,?_,?_⟩
  · simp [len]
  · have whole := NaturalRun.step t1 (.step t2 (.step t3 (.step t4 child)))
    convert whole using 1 <;> simp [state,List.append_assoc,Nat.add_comm]
    all_goals omega
  · simpa only [h0,List.append_assoc] using rep
  · have hs : h0[next]?=some scratch := by simp [h0,hn]
    simpa only [h0,scratch,List.append_assoc] using lookup_extend hs ex
end DirectedFlowCutGap.OriginalDispatch
