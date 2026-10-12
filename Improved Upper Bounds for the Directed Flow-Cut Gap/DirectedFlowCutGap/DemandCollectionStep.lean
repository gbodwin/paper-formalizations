import DirectedFlowCutGap.DemandRecordConstruction

namespace DirectedFlowCutGap.DemandCollection
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor
open GraphWalkExtension

def stepRecords (vs adjacency : List Bits) (rows : List Fraction) (next : ℕ) (x : Demand)
    (zs : List Record) : List Record :=
  match query vs adjacency rows x with
  | none => zs
  | some q => let payload := next+5+queryCells vs adjacency rows x
    ⟨x,q,⟨q.cost,payload,payload+1⟩⟩::zs

theorem step_return {heap : NaturalHeap} {x : Demand} {b tail result : ℕ} {zs : List Record}
    {vs adjacency : List Bits} {values : List Fraction} (N : ℕ)
    (occurrence : heap[x.occurrence]?=some (.pair x.record tail)) (demand : StoredDemand heap x)
    (shared : Shared heap b vs adjacency values) (tailRep : RecordList heap result zs)
    (rows : N ≤ adjacency.length)
    (cols : ∀ (i : ℕ) (hi : i<N),N ≤ (adjacency[i]'(lt_of_lt_of_le hi rows)).length)
    (hv : ∀ v∈vs,value v<N) (ht : value x.targetWord<N) (hc : ∀ v∈vs,value v<values.length)
    (valid : ∀ q,GraphDiscoveryProgram.minimize vs adjacency values x.sourceWord x.targetWord x.sourceWord=some q →
      ∀ w∈(CostedSupportProgram.edges vs adjacency q.edges x.sourceWord x.targetWord).map Prod.fst,value w<values.length)
    (next a : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 1604)
    (stack : List (Frame ℕ 1604)) (source : Bits) :
    ∃ ext root,
      ext.length=queryCells vs adjacency values x+(match query vs adjacency values x with | none => 5 | some _ => 8) ∧
      NaturalRun program (querySteps vs adjacency values x+(match query vs adjacency values x with | none => 28 | some _ => 33))
        (state heap next a b x.occurrence result (⟨pc,.r3,saved⟩::stack) source 1546) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      RecordList (heap++ext) root (stepRecords vs adjacency values next x zs) := by
  let frames := (⟨pc,.r3,saved⟩::stack)
  let ef : NaturalHeap := [.pair x.occurrence result]
  let h1 := heap++ef
  let n1 := next+1
  have dense1 : n1=h1.length := by simp [n1,h1,ef,hn]
  have frame1 : h1[next]?=some (.pair x.occurrence result) := by simp [h1,ef,hn]
  have occurrence1 : h1[x.occurrence]?=some (.pair x.record tail) := lookup_extend occurrence ef
  obtain ⟨ec,global,lc,contextRun,context⟩ := build_query_context (demand_extend demand ef)
    (shared_extend shared ef) n1 next result dense1 ⟨x.record,b,next,result⟩ 1550 frames source
  let h2 := h1++ec
  let n2 := n1+4
  have dense2 : n2=h2.length := by simp [n2,h2,dense1,lc]
  obtain ⟨eqr,chosen,lq,queryRun,chosenRep⟩ := query_return N
    (demand_extend (demand_extend demand ef) ec) context rows cols hv ht hc valid
    n2 b next dense2 ⟨x.record,b,next,global⟩ 1551 frames source
  let h3 := h2++eqr
  let n3 := n2+eqr.length
  have dense3 : n3=h3.length := by simp [n3,h3,dense2]
  have frame3 : h3[next]?=some (.pair x.occurrence result) :=
    lookup_extend (lookup_extend frame1 ec) eqr
  have tail3 : RecordList h3 result zs := records_extend (records_extend (records_extend tailRep ef) ec) eqr
  have t1546 : tickNatural program (state heap next a b x.occurrence result frames source 1546)=
      some ⟨state h1 n1 a b next result frames source 1547,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,h1,n1,ef,allocateNatural,Recipe.cell]
  have t1547 : tickNatural program (state h1 n1 a b next result frames source 1547)=
      some ⟨state h1 n1 x.occurrence b next result frames source 1548,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,frame1]
  have t1548 : tickNatural program (state h1 n1 x.occurrence b next result frames source 1548)=
      some ⟨state h1 n1 x.record b next result frames source 1549,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,occurrence1]
  have t1549 : tickNatural program (state h1 n1 x.record b next result frames source 1549)=
      some ⟨state h1 n1 x.record b next result (⟨1550,.r3,⟨x.record,b,next,result⟩⟩::frames) source 1580,[],0⟩ := by
    simp [tickNatural,program,state]
  have t1550 : tickNatural program (state h2 n2 x.record b next global frames source 1550)=
      some ⟨state h2 n2 x.record b next global (⟨1551,.r3,⟨x.record,b,next,global⟩⟩::frames) source 1592,[],0⟩ := by
    simp [tickNatural,program,state]
  have prefixRun : NaturalRun program (querySteps vs adjacency values x+25)
      (state heap next a b x.occurrence result frames source 1546) []
      (state h3 n3 x.record b next chosen frames source 1551) := by
    have all := run_append (.step t1546 (.step t1547 (.step t1548 (.step t1549 contextRun))))
      (.step t1550 queryRun)
    convert all using 1 <;> simp [Nat.add_assoc]; omega
  change GraphDiscoveryProgram.StoredOption h3 chosen (query vs adjacency values x) at chosenRep
  cases chosenEq : query vs adjacency values x with
  | none =>
    have chosenNil : h3[chosen]?=some .nil := by simpa only [chosenEq,GraphDiscoveryProgram.StoredOption,GraphRelaxationProgram.StoredOption] using chosenRep
    have branch : tickNatural program (state h3 n3 x.record b next chosen frames source 1551)=
        some ⟨state h3 n3 x.record b next chosen frames source 1560,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,chosenNil,tagBranch]
    obtain ⟨finish,rep⟩ := absent_return frame3 tail3 n3 x.record b chosen saved pc stack source
    let ext := ef++ec++eqr
    have len : ext.length=queryCells vs adjacency values x+5 := by simp [ext,ef,lc,lq];omega
    have endNext : next+ext.length=n3 := by simp [ext,ef,n3,n2,n1,lc];omega
    have endHeap : heap++ext=h3 := by simp [ext,h3,h2,h1,List.append_assoc]
    refine ⟨ext,result,by simpa [chosenEq] using len,?_,?_⟩
    · have all := run_append prefixRun (.step branch finish)
      simpa [chosenEq,endNext,endHeap,Nat.add_assoc] using all
    · simpa only [endHeap,stepRecords,chosenEq] using rep
  | some q =>
    have chosenWalk : StoredWalk h3 chosen q := by simpa only [chosenEq,GraphDiscoveryProgram.StoredOption,GraphRelaxationProgram.StoredOption] using chosenRep
    obtain ⟨er,cost,chosenPair,edgeRep,costRep⟩ := chosenWalk
    have chosenWalk' : StoredWalk h3 chosen q := ⟨er,cost,chosenPair,edgeRep,costRep⟩
    have branch : tickNatural program (state h3 n3 x.record b next chosen frames source 1551)=
        some ⟨state h3 n3 x.record b next chosen frames source 1552,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,chosenPair,tagBranch]
    obtain ⟨ep,lp,finish,rep⟩ := present_return frame3 tail3 chosenWalk' n3 x.record b dense3 saved pc stack source
    let ext := ef++ec++eqr++ep
    have len : ext.length=queryCells vs adjacency values x+8 := by simp [ext,ef,lc,lq,lp];omega
    have endNext : next+ext.length=n3+3 := by simp [ext,ef,n3,n2,n1,lc,lp];omega
    have endHeap : heap++ext=h3++ep := by simp [ext,h3,h2,h1,List.append_assoc]
    have payload : n3=next+5+queryCells vs adjacency values x := by dsimp [n3,n2,n1];omega
    refine ⟨ext,n3+2,by simpa [chosenEq] using len,?_,?_⟩
    · have all := run_append prefixRun (.step branch finish)
      simpa [chosenEq,endNext,endHeap,Nat.add_assoc] using all
    · simpa only [endHeap,stepRecords,chosenEq,payload] using rep

end DirectedFlowCutGap.DemandCollection
