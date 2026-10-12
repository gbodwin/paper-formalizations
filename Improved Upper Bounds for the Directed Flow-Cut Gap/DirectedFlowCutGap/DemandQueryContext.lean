import DirectedFlowCutGap.DemandCollectionProgram

namespace DirectedFlowCutGap.DemandCollection
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor

theorem build_query_context {heap : NaturalHeap} {x : Demand} {b : ℕ}
    {vs adjacency : List Bits} {rows : List Fraction}
    (demand : StoredDemand heap x) (shared : Shared heap b vs adjacency rows)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 1604)
    (stack : List (Frame ℕ 1604)) (source : Bits) :
    ∃ ext root,ext.length=4 ∧
      NaturalRun program 12
        (state heap next x.record b c d (⟨pc,.r3,saved⟩::stack) source 1580) []
        (state (heap++ext) (next+4) saved.a saved.b saved.c root stack source pc) ∧
      GraphDiscoveryProgram.GlobalContext (heap++ext) root vs adjacency rows x.sourceWord x.targetWord := by
  obtain ⟨sr,tr,hpair,hsource,htarget⟩ := demand
  obtain ⟨er,bundle,matrix,table,hshared,hbundle,hvertices,hadjacency,hrows⟩ := shared
  let frames := (⟨pc,.r3,saved⟩::stack)
  let e1 : NaturalHeap := [.pair table sr]
  let e2 : NaturalHeap := [.pair matrix next]
  let e3 : NaturalHeap := [.pair er (next+1)]
  let e4 : NaturalHeap := [.pair tr (next+2)]
  let h1 := heap++e1
  let h2 := h1++e2
  let h3 := h2++e3
  let h4 := h3++e4
  have dense1 : next+1=h1.length := by simp [h1,e1,hn]
  have dense2 : next+2=h2.length := by simp [h2,h1,e2,e1,hn]
  have dense3 : next+3=h3.length := by simp [h3,h2,h1,e3,e2,e1,hn]
  have new1 : h1[next]?=some (.pair table sr) := by simp [h1,e1,hn]
  have new2 : h2[next+1]?=some (.pair matrix next) := by rw [dense1];simp [h2,e2]
  have new3 : h3[next+2]?=some (.pair er (next+1)) := by rw [dense2];simp [h3,e3]
  have new4 : h4[next+3]?=some (.pair tr (next+2)) := by rw [dense3];simp [h4,e4]
  have shared1 : h1[b]?=some (.pair er bundle) := lookup_extend hshared e1
  have bundle1 : h1[bundle]?=some (.pair matrix table) := lookup_extend hbundle e1
  have shared2 : h2[b]?=some (.pair er bundle) := lookup_extend shared1 e2
  have t1580 : tickNatural program (state heap next x.record b c d frames source 1580)=
      some ⟨state heap next x.record b sr d frames source 1581,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hpair]
  have t1581 : tickNatural program (state heap next x.record b sr d frames source 1581)=
      some ⟨state heap next x.record b sr tr frames source 1582,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hpair]
  have t1582 : tickNatural program (state heap next x.record b sr tr frames source 1582)=
      some ⟨state heap next bundle b sr tr frames source 1583,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hshared]
  have t1583 : tickNatural program (state heap next bundle b sr tr frames source 1583)=
      some ⟨state heap next table b sr tr frames source 1584,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hbundle]
  have t1584 : tickNatural program (state heap next table b sr tr frames source 1584)=
      some ⟨state h1 (next+1) next b sr tr frames source 1585,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,h1,e1,allocateNatural,Recipe.cell]
  have t1585 : tickNatural program (state h1 (next+1) next b sr tr frames source 1585)=
      some ⟨state h1 (next+1) next b bundle tr frames source 1586,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,shared1]
  have t1586 : tickNatural program (state h1 (next+1) next b bundle tr frames source 1586)=
      some ⟨state h1 (next+1) next b matrix tr frames source 1587,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,bundle1]
  have t1587 : tickNatural program (state h1 (next+1) next b matrix tr frames source 1587)=
      some ⟨state h2 (next+2) (next+1) b matrix tr frames source 1588,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,h2,e2,allocateNatural,Recipe.cell,Nat.add_assoc]
  have t1588 : tickNatural program (state h2 (next+2) (next+1) b matrix tr frames source 1588)=
      some ⟨state h2 (next+2) (next+1) er matrix tr frames source 1589,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,shared2]
  have t1589 : tickNatural program (state h2 (next+2) (next+1) er matrix tr frames source 1589)=
      some ⟨state h3 (next+3) (next+2) er matrix tr frames source 1590,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,h3,e3,allocateNatural,Recipe.cell,Nat.add_assoc]
  have t1590 : tickNatural program (state h3 (next+3) (next+2) er matrix tr frames source 1590)=
      some ⟨state h4 (next+4) (next+2) er matrix (next+3) frames source 1591,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,h4,e4,allocateNatural,Recipe.cell,Nat.add_assoc]
  have t1591 : tickNatural program (state h4 (next+4) (next+2) er matrix (next+3) frames source 1591)=
      some ⟨state h4 (next+4) saved.a saved.b saved.c (next+3) stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,frames]
  have run : NaturalRun program 12 (state heap next x.record b c d frames source 1580) []
      (state h4 (next+4) saved.a saved.b saved.c (next+3) stack source pc) := (.step t1580 (.step t1581 (.step t1582 (.step t1583 (.step t1584 (.step t1585 (.step t1586 (.step t1587 (.step t1588 (.step t1589 (.step t1590 (.step t1591 (.done _)))))))))))))
  let ext := e1++e2++e3++e4
  have he : heap++ext=h4 := by simp [ext,h4,h3,h2,h1,List.append_assoc]
  refine ⟨ext,next+3,by simp [ext,e1,e2,e3,e4],?_,?_⟩
  · simpa only [he] using run
  · refine ⟨tr,next+2,er,next+1,matrix,next,?_,?_,?_,boolList_extend htarget ext,
      GraphDiscoveryProgram.vertices_extend hvertices ext,GraphAdjacencyProgram.matrix_extend hadjacency ext,?_⟩
    · simpa only [he] using new4
    · simpa only [he] using lookup_extend new3 e4
    · simpa only [he] using lookup_extend (lookup_extend new2 e3) e4
    · refine ⟨table,sr,?_,BinaryIndexedPairRead.table_extend hrows ext,boolList_extend hsource ext⟩
      simpa only [he] using lookup_extend (lookup_extend (lookup_extend new1 e2) e3) e4

end DirectedFlowCutGap.DemandCollection
