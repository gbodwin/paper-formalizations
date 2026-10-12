import DirectedFlowCutGap.DemandQueryCall

namespace DirectedFlowCutGap.DemandCollection
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor
open GraphWalkExtension

theorem absent_return {heap : NaturalHeap} {frame tail : ℕ} {x : Demand} {zs : List Record}
    (hf : heap[frame]?=some (.pair x.occurrence tail)) (ht : RecordList heap tail zs)
    (next a b d : ℕ) (saved : Registers ℕ) (pc : Fin 1604)
    (stack : List (Frame ℕ 1604)) (source : Bits) :
    NaturalRun program 2 (state heap next a b frame d (⟨pc,.r3,saved⟩::stack) source 1560) []
      (state heap next saved.a saved.b saved.c tail stack source pc) ∧ RecordList heap tail zs := by
  have t1560 : tickNatural program (state heap next a b frame d (⟨pc,.r3,saved⟩::stack) source 1560)=
      some ⟨state heap next a b frame tail (⟨pc,.r3,saved⟩::stack) source 1561,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hf]
  have t1561 : tickNatural program (state heap next a b frame tail (⟨pc,.r3,saved⟩::stack) source 1561)=
      some ⟨state heap next saved.a saved.b saved.c tail stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  exact ⟨.step t1560 (.step t1561 (.done _)),ht⟩

theorem present_return {heap : NaturalHeap} {frame tail root : ℕ} {x : Demand}
    {q : Walk} {zs : List Record} (hf : heap[frame]?=some (.pair x.occurrence tail))
    (ht : RecordList heap tail zs) (hq : StoredWalk heap root q)
    (next a b : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 1604)
    (stack : List (Frame ℕ 1604)) (source : Bits) :
    ∃ ext,ext.length=3 ∧
      NaturalRun program 7
        (state heap next a b frame root (⟨pc,.r3,saved⟩::stack) source 1552) []
        (state (heap++ext) (next+3) saved.a saved.b saved.c (next+2) stack source pc) ∧
      RecordList (heap++ext) (next+2) (⟨x,q,⟨q.cost,next,next+1⟩⟩::zs) := by
  obtain ⟨edgeRoot,costRoot,hroot,hedges,hcost⟩ := hq
  let frames := (⟨pc,.r3,saved⟩::stack)
  let e1 : NaturalHeap := [.pair x.occurrence root]
  let e2 : NaturalHeap := [.pair costRoot next]
  let e3 : NaturalHeap := [.pair (next+1) tail]
  let h1 := heap++e1
  let h2 := h1++e2
  let h3 := h2++e3
  have dense1 : next+1=h1.length := by simp [h1,e1,hn]
  have dense2 : next+2=h2.length := by simp [h2,h1,e2,e1,hn]
  have new1 : h1[next]?=some (.pair x.occurrence root) := by simp [h1,e1,hn]
  have new2 : h2[next+1]?=some (.pair costRoot next) := by rw [dense1];simp [h2,e2]
  have new3 : h3[next+2]?=some (.pair (next+1) tail) := by rw [dense2];simp [h3,e3]
  have root1 : h1[root]?=some (.pair edgeRoot costRoot) := lookup_extend hroot e1
  have frame2 : h2[frame]?=some (.pair x.occurrence tail) := lookup_extend (lookup_extend hf e1) e2
  have t1552 : tickNatural program (state heap next a b frame root frames source 1552)=
      some ⟨state heap next x.occurrence b frame root frames source 1553,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hf]
  have t1553 : tickNatural program (state heap next x.occurrence b frame root frames source 1553)=
      some ⟨state h1 (next+1) next b frame root frames source 1554,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,h1,e1,allocateNatural,Recipe.cell]
  have t1554 : tickNatural program (state h1 (next+1) next b frame root frames source 1554)=
      some ⟨state h1 (next+1) next b frame costRoot frames source 1555,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,root1]
  have t1555 : tickNatural program (state h1 (next+1) next b frame costRoot frames source 1555)=
      some ⟨state h2 (next+2) (next+1) b frame costRoot frames source 1556,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,h2,e2,allocateNatural,Recipe.cell,Nat.add_assoc]
  have t1556 : tickNatural program (state h2 (next+2) (next+1) b frame costRoot frames source 1556)=
      some ⟨state h2 (next+2) (next+1) b tail costRoot frames source 1557,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,frame2]
  have t1557 : tickNatural program (state h2 (next+2) (next+1) b tail costRoot frames source 1557)=
      some ⟨state h3 (next+3) (next+1) b tail (next+2) frames source 1558,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,h3,e3,allocateNatural,Recipe.cell,Nat.add_assoc]
  have t1558 : tickNatural program (state h3 (next+3) (next+1) b tail (next+2) frames source 1558)=
      some ⟨state h3 (next+3) saved.a saved.b saved.c (next+2) stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,frames,Registers.get,Registers.set]
  let ext := e1++e2++e3
  have he : heap++ext=h3 := by simp [ext,h3,h2,h1,List.append_assoc]
  refine ⟨ext,by simp [ext,e1,e2,e3],?_,?_⟩
  · have all : NaturalRun program 7 (state heap next a b frame root frames source 1552) []
        (state h3 (next+3) saved.a saved.b saved.c (next+2) stack source pc) :=
      .step t1552 (.step t1553 (.step t1554 (.step t1555 (.step t1556 (.step t1557 (.step t1558 (.done _)))))))
    simpa only [he] using all
  · apply RecordList.cons
    · simpa only [he] using new3
    · refine ⟨⟨rfl,costRoot,?_,RationalComparisonProgram.stored_extend hcost ext⟩,rfl,root,?_,?_⟩
      · simpa only [he] using lookup_extend new2 e3
      · simpa only [he] using lookup_extend (lookup_extend new1 e2) e3
      · exact walk_extend ⟨edgeRoot,costRoot,hroot,hedges,hcost⟩ ext
    · exact records_extend ht ext

end DirectedFlowCutGap.DemandCollection
