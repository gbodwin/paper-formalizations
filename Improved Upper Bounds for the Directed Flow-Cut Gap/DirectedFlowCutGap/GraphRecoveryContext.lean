import DirectedFlowCutGap.GraphRecoveryController

namespace DirectedFlowCutGap.GraphRecoveryController
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor
open GraphWalkExtension

theorem build_context {heap : NaturalHeap} {b d : ℕ} {vs adjacency : List Bits}
    {rows : List Fraction} {sw target : Bits} {q : Walk}
    (context : GraphDiscoveryProgram.GlobalContext heap b vs adjacency rows sw target)
    (candidate : StoredWalk heap d q) (next a c : ℕ) (hn : next=heap.length)
    (frames : List (Frame ℕ 1344)) (source : Bits) :
    ∃ ext enumRoot sourceRoot scratch,ext.length=4 ∧
      NaturalRun program 15 (state heap next a b c d frames source 1314) []
        (state (heap++ext) (next+4) enumRoot (next+3) sourceRoot scratch frames source 1329) ∧
      SupportRecoveryProgram.Vertices (heap++ext) enumRoot vs ∧
      CostedSupportProgram.Context (heap++ext) (next+3) vs adjacency q.edges target rows sw ∧
      BoolList (heap++ext) sourceRoot sw := by
  obtain ⟨tr,bundle,enumRoot,mix,matrix,cost,hp,hb,hm,ht,he,ha,hc⟩ := context
  obtain ⟨table,sourceRoot,hcost,tableRep,sourceRep⟩ := hc
  obtain ⟨edgeRoot,fractionRoot,hrecord,edgesRep,_⟩ := candidate
  let e1 : NaturalHeap := [.pair matrix edgeRoot]
  let e2 : NaturalHeap := [.pair enumRoot next]
  let e3 : NaturalHeap := [.pair tr (next+1)]
  let e4 : NaturalHeap := [.pair (next+2) cost]
  let h1 := heap++e1
  let h2 := h1++e2
  let h3 := h2++e3
  let h4 := h3++e4
  have dense1 : next+1=h1.length := by simp [h1,e1,hn]
  have dense2 : next+2=h2.length := by simp [h2,h1,e2,e1,hn]
  have dense3 : next+3=h3.length := by simp [h3,h2,h1,e3,e2,e1,hn]
  have new1 : h1[next]?=some (.pair matrix edgeRoot) := by simp [h1,e1,hn]
  have new2 : h2[next+1]?=some (.pair enumRoot next) := by rw [dense1];simp [h2,e2]
  have new3 : h3[next+2]?=some (.pair tr (next+1)) := by rw [dense2];simp [h3,e3]
  have new4 : h4[next+3]?=some (.pair (next+2) cost) := by rw [dense3];simp [h4,e4]
  have n1last : h4[next]?=some (.pair matrix edgeRoot) := lookup_extend (lookup_extend (lookup_extend new1 e2) e3) e4
  have n2last : h4[next+1]?=some (.pair enumRoot next) := lookup_extend (lookup_extend new2 e3) e4
  have n3last : h4[next+2]?=some (.pair tr (next+1)) := lookup_extend new3 e4
  have hp1 : h1[b]?=some (.pair tr bundle) := lookup_extend hp e1
  have hb1 : h1[bundle]?=some (.pair enumRoot mix) := lookup_extend hb e1
  have hp2 : h2[b]?=some (.pair tr bundle) := lookup_extend hp1 e2
  have hm3 : h3[mix]?=some (.pair matrix cost) := lookup_extend (lookup_extend (lookup_extend hm e1) e2) e3
  have hc4 : h4[cost]?=some (.pair table sourceRoot) := lookup_extend (lookup_extend (lookup_extend (lookup_extend hcost e1) e2) e3) e4
  have t1314 : tickNatural program (state heap next a b c d frames source 1314)=
      some ⟨state heap next a b c edgeRoot frames source 1315,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hrecord]
  have t1315 : tickNatural program (state heap next a b c edgeRoot frames source 1315)=
      some ⟨state heap next a b bundle edgeRoot frames source 1316,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hp]
  have t1316 : tickNatural program (state heap next a b bundle edgeRoot frames source 1316)=
      some ⟨state heap next a b mix edgeRoot frames source 1317,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hb]
  have t1317 : tickNatural program (state heap next a b mix edgeRoot frames source 1317)=
      some ⟨state heap next matrix b mix edgeRoot frames source 1318,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hm]
  have t1318 : tickNatural program (state heap next matrix b mix edgeRoot frames source 1318)=
      some ⟨state h1 (next+1) next b mix edgeRoot frames source 1319,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,h1,e1,allocateNatural,Recipe.cell]
  have t1319 : tickNatural program (state h1 (next+1) next b mix edgeRoot frames source 1319)=
      some ⟨state h1 (next+1) next b mix bundle frames source 1320,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hp1]
  have t1320 : tickNatural program (state h1 (next+1) next b mix bundle frames source 1320)=
      some ⟨state h1 (next+1) next b mix enumRoot frames source 1321,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hb1]
  have t1321 : tickNatural program (state h1 (next+1) next b mix enumRoot frames source 1321)=
      some ⟨state h2 (next+2) (next+1) b mix enumRoot frames source 1322,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,h2,e2,allocateNatural,Recipe.cell,Nat.add_assoc]
  have t1322 : tickNatural program (state h2 (next+2) (next+1) b mix enumRoot frames source 1322)=
      some ⟨state h2 (next+2) (next+1) b mix tr frames source 1323,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hp2]
  have t1323 : tickNatural program (state h2 (next+2) (next+1) b mix tr frames source 1323)=
      some ⟨state h3 (next+3) (next+2) b mix tr frames source 1324,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,h3,e3,allocateNatural,Recipe.cell,Nat.add_assoc]
  have t1324 : tickNatural program (state h3 (next+3) (next+2) b mix tr frames source 1324)=
      some ⟨state h3 (next+3) (next+2) b cost tr frames source 1325,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hm3]
  have t1325 : tickNatural program (state h3 (next+3) (next+2) b cost tr frames source 1325)=
      some ⟨state h4 (next+4) (next+2) (next+3) cost tr frames source 1326,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,h4,e4,allocateNatural,Recipe.cell,Nat.add_assoc]
  have t1326 : tickNatural program (state h4 (next+4) (next+2) (next+3) cost tr frames source 1326)=
      some ⟨state h4 (next+4) (next+1) (next+3) cost tr frames source 1327,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,n3last]
  have t1327 : tickNatural program (state h4 (next+4) (next+1) (next+3) cost tr frames source 1327)=
      some ⟨state h4 (next+4) enumRoot (next+3) cost tr frames source 1328,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,n2last]
  have t1328 : tickNatural program (state h4 (next+4) enumRoot (next+3) cost tr frames source 1328)=
      some ⟨state h4 (next+4) enumRoot (next+3) sourceRoot tr frames source 1329,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hc4]
  let ext := e1++e2++e3++e4
  have trace : NaturalRun program 15 (state heap next a b c d frames source 1314) []
      (state h4 (next+4) enumRoot (next+3) sourceRoot tr frames source 1329) :=
    .step t1314 (.step t1315 (.step t1316 (.step t1317 (.step t1318 (.step t1319 (.step t1320 (.step t1321 (.step t1322 (.step t1323 (.step t1324 (.step t1325 (.step t1326 (.step t1327 (.step t1328 (.done _)))))))))))))))
  have heapEq : heap++ext=h4 := by simp [ext,h4,h3,h2,h1,List.append_assoc]
  refine ⟨ext,enumRoot,sourceRoot,tr,by simp [ext,e1,e2,e3,e4],?_,?_,?_,?_⟩
  · simpa only [heapEq] using trace
  · exact GraphDiscoveryProgram.vertices_extend he ext
  · refine ⟨next+2,cost,?_,?_,?_⟩
    · simpa only [heapEq] using new4
    · refine ⟨tr,next+1,enumRoot,next,?_,?_,boolList_extend ht ext,
        GraphDiscoveryProgram.vertices_extend he ext,?_⟩
      · simpa only [heapEq] using n3last
      · simpa only [heapEq] using n2last
      · exact ⟨matrix,edgeRoot,by simpa only [heapEq] using n1last,
          GraphAdjacencyProgram.matrix_extend ha ext,edgeList_extend edgesRep ext⟩
    · exact ⟨table,sourceRoot,lookup_extend hcost ext,
        BinaryIndexedPairRead.table_extend tableRep ext,boolList_extend sourceRep ext⟩
  · exact boolList_extend sourceRep ext

end DirectedFlowCutGap.GraphRecoveryController
