import DirectedFlowCutGap.OracleEmptyChoice

namespace DirectedFlowCutGap.OracleChoice
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor GraphWalkExtension

/-- Literal field reads recover the original demand and path from the selected
record, then call the actual mask constructor on that very stored edge list. -/
theorem selected_mask_run {heap : NaturalHeap} {z : DemandCollection.Record}
    (hz : DemandCollection.StoredRecord heap z) (hd : DemandCollection.StoredDemand heap z.demand)
    {tail b vertices capacities : ℕ} (ho : heap[z.demand.occurrence]?=some (.pair z.demand.record tail))
    (hb : heap[b]?=some (.pair vertices capacities)) {vs : List Bits}
    (hv : GraphDiscoveryProgram.Vertices heap vertices vs)
    (next c d : ℕ) (hn : next=heap.length) (stack : List (Frame ℕ 484)) (source : Bits) :
    ∃ ext root,ext.length=OracleMask.cells z.demand.sourceWord z.demand.targetWord z.path.edges vs+2 ∧
      NaturalRun program (OracleMask.steps z.demand.sourceWord z.demand.targetWord z.path.edges vs+13)
        (state heap next z.item.address b c d stack source 410) []
        (state (heap++ext) (next+ext.length) vertices (next+1) next root stack source 421) ∧
      BoolList (heap++ext) root (OracleMask.mask z.demand.sourceWord z.demand.targetWord z.path.edges vs) ∧
      (heap++ext)[next]?=some (.pair z.item.address b) := by
  obtain ⟨⟨_,score,hi,_⟩,_,pathRoot,hpayload,hw⟩ := hz
  obtain ⟨edges,cost,hpath,hedges,_⟩ := hw
  obtain ⟨sr,tr,hdemand,hs,ht⟩ := hd
  let frame : Cell ℕ := .pair z.item.address b
  let maskContext : Cell ℕ := .pair z.demand.record edges
  let h1 := heap++[frame]
  let h2 := h1++[maskContext]
  have hn2 : next+2=h2.length := by simp [h2,h1,hn]
  have input : GraphDiscoveryProgram.Vertices h2 vertices vs := by
    exact GraphDiscoveryProgram.vertices_extend (GraphDiscoveryProgram.vertices_extend hv [frame]) [maskContext]
  have ctx : OracleMask.Context h2 (next+1) z.demand.sourceWord z.demand.targetWord z.path.edges := by
    refine ⟨z.demand.record,edges,sr,tr,?_,?_,?_,?_,?_⟩
    · simp [h2,h1,maskContext,hn]
    · exact lookup_extend (lookup_extend hdemand [frame]) [maskContext]
    · exact boolList_extend (boolList_extend hs [frame]) [maskContext]
    · exact boolList_extend (boolList_extend ht [frame]) [maskContext]
    · exact edgeList_extend (edgeList_extend hedges [frame]) [maskContext]
  obtain ⟨em,rm,lm,body,rep⟩ := mask_return input ctx (next+2) next d hn2
    ⟨vertices,next+1,next,d⟩ 421 stack source
  have t410 : tickNatural program (state heap next z.item.address b c d stack source 410)=
      some ⟨state h1 (next+1) z.item.address b next d stack source 411,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,h1,frame]
  have t411 : tickNatural program (state h1 (next+1) z.item.address b next d stack source 411)=
      some ⟨state h1 (next+1) z.item.address b next d stack source 412,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,tagBranch,h1,lookup_extend hi [frame]]
  have t412 : tickNatural program (state h1 (next+1) z.item.address b next d stack source 412)=
      some ⟨state h1 (next+1) z.item.payload b next d stack source 413,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,h1,lookup_extend hi [frame]]
  have t413 : tickNatural program (state h1 (next+1) z.item.payload b next d stack source 413)=
      some ⟨state h1 (next+1) z.item.payload z.demand.occurrence next d stack source 414,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,h1,lookup_extend hpayload [frame]]
  have t414 : tickNatural program (state h1 (next+1) z.item.payload z.demand.occurrence next d stack source 414)=
      some ⟨state h1 (next+1) z.item.payload z.demand.record next d stack source 415,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,h1,lookup_extend ho [frame]]
  have t415 : tickNatural program (state h1 (next+1) z.item.payload z.demand.record next d stack source 415)=
      some ⟨state h1 (next+1) pathRoot z.demand.record next d stack source 416,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,h1,lookup_extend hpayload [frame]]
  have t416 : tickNatural program (state h1 (next+1) pathRoot z.demand.record next d stack source 416)=
      some ⟨state h1 (next+1) edges z.demand.record next d stack source 417,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,h1,lookup_extend hpath [frame]]
  have t417 : tickNatural program (state h1 (next+1) edges z.demand.record next d stack source 417)=
      some ⟨state h2 (next+2) edges (next+1) next d stack source 418,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,h2,h1,maskContext]
  have t418 : tickNatural program (state h2 (next+2) edges (next+1) next d stack source 418)=
      some ⟨state h2 (next+2) b (next+1) next d stack source 419,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,h2,h1,frame,maskContext,hn]
  have t419 : tickNatural program (state h2 (next+2) b (next+1) next d stack source 419)=
      some ⟨state h2 (next+2) vertices (next+1) next d stack source 420,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,lookup_extend hb [frame,maskContext],h2,h1]
  have t420 : tickNatural program (state h2 (next+2) vertices (next+1) next d stack source 420)=
      some ⟨state h2 (next+2) vertices (next+1) next d (⟨421,.r3,⟨vertices,next+1,next,d⟩⟩::stack) source 150,[],0⟩ := by
    simp [tickNatural,program,state]
  let ext : NaturalHeap := [frame,maskContext]++em
  refine ⟨ext,rm,by simp [ext,lm],?_,?_,?_⟩
  · have all := NaturalRun.step t410 (NaturalRun.step t411 (NaturalRun.step t412 (NaturalRun.step t413 (NaturalRun.step t414 (NaturalRun.step t415 (NaturalRun.step t416 (NaturalRun.step t417 (NaturalRun.step t418 (NaturalRun.step t419 (NaturalRun.step t420 (body)))))))))))
    convert all using 1 <;> simp [ext,h2,h1,state,List.append_assoc]
    all_goals omega
  · simpa [ext,h2,h1,List.append_assoc] using rep
  · simp [ext,frame,hn]

end DirectedFlowCutGap.OracleChoice
