import DirectedFlowCutGap.AvoidingGraphContextProgram

namespace DirectedFlowCutGap.AvoidingGraphContext
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor
open CanonicalRationalSum (StoredList list_extend)

theorem construct_return {heap : NaturalHeap} {a b : ℕ} {vs adjacency : List Bits}
    {rows : List Fraction} {sw target : Bits}
    (vertices : GraphDiscoveryProgram.Vertices heap a vs) (context : Input heap b adjacency rows sw target)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 20)
    (stack : List (Frame ℕ 20)) (source : Bits) :
    ∃ ext root,ext.length=5 ∧ NaturalRun program 15
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 0) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      GraphDiscoveryProgram.GlobalContext (heap++ext) root vs adjacency rows sw target := by
  obtain ⟨ep,sr,tr,detail,ar,cost,hp,he,hd,hs,ht,ha,hc⟩ := context
  let frames : List (Frame ℕ 20) := ⟨pc,.r3,saved⟩::stack
  let h1 : NaturalHeap := heap++[.pair a b]
  let h2 : NaturalHeap := heap++[.pair a b,.pair cost sr]
  let h3 : NaturalHeap := heap++[.pair a b,.pair cost sr,.pair ar (next+1)]
  let h4 : NaturalHeap := heap++[.pair a b,.pair cost sr,.pair ar (next+1),.pair a (next+2)]
  let h5 : NaturalHeap := heap++[.pair a b,.pair cost sr,.pair ar (next+1),.pair a (next+2),.pair tr (next+3)]
  have hp1 : h1[b]?=some (.pair ep detail) := lookup_extend hp _
  have he1 : h1[ep]?=some (.pair sr tr) := lookup_extend he _
  have hd1 : h1[detail]?=some (.pair ar cost) := lookup_extend hd _
  have hsave1 : h1[next]?=some (.pair a b) := by simp [h1,hn]
  have hp2 : h2[b]?=some (.pair ep detail) := lookup_extend hp _
  have he2 : h2[ep]?=some (.pair sr tr) := lookup_extend he _
  have hd2 : h2[detail]?=some (.pair ar cost) := lookup_extend hd _
  have hsave2 : h2[next]?=some (.pair a b) := by simp [h2,hn]
  have hp3 : h3[b]?=some (.pair ep detail) := lookup_extend hp _
  have he3 : h3[ep]?=some (.pair sr tr) := lookup_extend he _
  have hd3 : h3[detail]?=some (.pair ar cost) := lookup_extend hd _
  have hsave3 : h3[next]?=some (.pair a b) := by simp [h3,hn]
  have hp4 : h4[b]?=some (.pair ep detail) := lookup_extend hp _
  have he4 : h4[ep]?=some (.pair sr tr) := lookup_extend he _
  have hd4 : h4[detail]?=some (.pair ar cost) := lookup_extend hd _
  have hsave4 : h4[next]?=some (.pair a b) := by simp [h4,hn]
  have hp5 : h5[b]?=some (.pair ep detail) := lookup_extend hp _
  have he5 : h5[ep]?=some (.pair sr tr) := lookup_extend he _
  have hd5 : h5[detail]?=some (.pair ar cost) := lookup_extend hd _
  have hsave5 : h5[next]?=some (.pair a b) := by simp [h5,hn]
  have t0 : tickNatural program (state heap next a b c d frames source 0)=
      some ⟨state h1 (next+1) a b next d frames source 1,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,h1]
  have t1 : tickNatural program (state h1 (next+1) a b next d frames source 1)=
      some ⟨state h1 (next+1) detail b next d frames source 2,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hp1]
  have t2 : tickNatural program (state h1 (next+1) detail b next d frames source 2)=
      some ⟨state h1 (next+1) detail b next cost frames source 3,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hd1]
  have t3 : tickNatural program (state h1 (next+1) detail b next cost frames source 3)=
      some ⟨state h1 (next+1) detail ep next cost frames source 4,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hp1]
  have t4 : tickNatural program (state h1 (next+1) detail ep next cost frames source 4)=
      some ⟨state h1 (next+1) detail sr next cost frames source 5,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,he1]
  have t5 : tickNatural program (state h1 (next+1) detail sr next cost frames source 5)=
      some ⟨state h2 (next+2) detail sr next (next+1) frames source 6,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,h1,h2,List.append_assoc,Nat.add_assoc]
  have t6 : tickNatural program (state h2 (next+2) detail sr next (next+1) frames source 6)=
      some ⟨state h2 (next+2) ar sr next (next+1) frames source 7,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hd2]
  have t7 : tickNatural program (state h2 (next+2) ar sr next (next+1) frames source 7)=
      some ⟨state h3 (next+3) ar sr next (next+2) frames source 8,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,h2,h3,List.append_assoc,Nat.add_assoc]
  have t8 : tickNatural program (state h3 (next+3) ar sr next (next+2) frames source 8)=
      some ⟨state h3 (next+3) a sr next (next+2) frames source 9,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hsave3]
  have t9 : tickNatural program (state h3 (next+3) a sr next (next+2) frames source 9)=
      some ⟨state h4 (next+4) a sr next (next+3) frames source 10,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,h3,h4,List.append_assoc,Nat.add_assoc]
  have t10 : tickNatural program (state h4 (next+4) a sr next (next+3) frames source 10)=
      some ⟨state h4 (next+4) a b next (next+3) frames source 11,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hsave4]
  have t11 : tickNatural program (state h4 (next+4) a b next (next+3) frames source 11)=
      some ⟨state h4 (next+4) a ep next (next+3) frames source 12,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hp4]
  have t12 : tickNatural program (state h4 (next+4) a ep next (next+3) frames source 12)=
      some ⟨state h4 (next+4) a tr next (next+3) frames source 13,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,he4]
  have t13 : tickNatural program (state h4 (next+4) a tr next (next+3) frames source 13)=
      some ⟨state h5 (next+5) a tr next (next+4) frames source 14,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,h4,h5,List.append_assoc,Nat.add_assoc]
  have t14 : tickNatural program (state h5 (next+5) a tr next (next+4) frames source 14)=
      some ⟨state h5 (next+5) saved.a saved.b saved.c (next+4) stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,frames]
  let ext : NaturalHeap := [.pair a b,.pair cost sr,.pair ar (next+1),.pair a (next+2),.pair tr (next+3)]
  refine ⟨ext,next+4,rfl,?_,?_⟩
  · simpa [ext,h5,frames] using
      NaturalRun.step t0 (NaturalRun.step t1 (NaturalRun.step t2 (NaturalRun.step t3 (NaturalRun.step t4 (NaturalRun.step t5 (NaturalRun.step t6 (NaturalRun.step t7 (NaturalRun.step t8 (NaturalRun.step t9 (NaturalRun.step t10 (NaturalRun.step t11 (NaturalRun.step t12 (NaturalRun.step t13 (NaturalRun.step t14 (.done _)))))))))))))))
  · change GraphDiscoveryProgram.GlobalContext h5 (next+4) vs adjacency rows sw target
    refine ⟨tr,next+3,a,next+2,ar,next+1,?_,?_,?_,boolList_extend ht _,
      GraphDiscoveryProgram.vertices_extend vertices _,GraphAdjacencyProgram.matrix_extend ha _,?_⟩
    · simp [h5,hn]
    · simp [h5,hn]
    · simp [h5,hn]
    · exact ⟨cost,sr,by simp [h5,hn],PackingGraphContext.row_table (list_extend hc _),boolList_extend hs _⟩
end DirectedFlowCutGap.AvoidingGraphContext
