import DirectedFlowCutGap.PackingSourceInputCalls

namespace DirectedFlowCutGap.PackingSourceInput
open BinaryArithmetic ImmutableReferenceSimulation WordPairTableRead

def encode (capacity matrix demands : List (Bits × Bits)) : Bits :=
  SourceRowTableProgram.encode capacity++SourceRowTableProgram.encode matrix++
    SourceRowTableProgram.encode demands

def instructions (capacity matrix demands : List (Bits × Bits)) : ℕ :=
  SourceRowTableProgram.steps capacity+SourceRowTableProgram.steps matrix+
    SourceRowTableProgram.steps demands+7*matrix.length+19

/-- All three tables are read from the actual source, and the same returned
matrix table is projected into the final matrix spine. -/
theorem prepare (capacity matrix demands : List (Bits × Bits)) (suffix : Bits)
    (heap : NaturalHeap) (next a b c d : ℕ) (hn : next=heap.length) :
    ∃ ext cap mat dem, NaturalRun program (instructions capacity matrix demands)
      (state heap next a b c d [] (encode capacity matrix demands++suffix) 48)
      ((encode capacity matrix demands).map Event.request)
      (state (heap++ext) (next+ext.length) cap mat mat dem [] suffix 56) ∧
      Table (heap++ext) cap capacity ∧ GraphAdjacencyProgram.Matrix (heap++ext) mat
        (matrix.map Prod.fst) ∧ Table (heap++ext) dem demands := by
  let tail2 := SourceRowTableProgram.encode demands++suffix
  let tail1 := SourceRowTableProgram.encode matrix++tail2
  obtain ⟨e1,cap,l1,r1,hcap⟩ := read_table capacity tail1 heap next a b c d hn ⟨a,b,c,d⟩ .r0 49 []
  let h1 := heap++e1
  have n1 : next+e1.length=h1.length := by simp [h1,hn]
  obtain ⟨e2,rawMat,l2,r2,hmat⟩ := read_table matrix tail2 h1 (next+e1.length)
    cap b c d n1 ⟨cap,b,c,d⟩ .r1 50 []
  let h2 := h1++e2
  have n2 : next+e1.length+e2.length=h2.length := by simp [h2,n1]
  obtain ⟨e3,dem,l3,r3,hdem⟩ := read_table demands suffix h2 (next+e1.length+e2.length)
    cap rawMat c d n2 ⟨cap,rawMat,c,d⟩ .r3 51 []
  let h3 := h2++e3
  have n3 : next+e1.length+e2.length+e3.length=h3.length := by simp [h3,n2]
  have hm3 : Table h3 rawMat matrix := BinaryIndexedPairRead.table_extend hmat e3
  obtain ⟨e4,mat,l4,r4,hm⟩ := project_matrix hm3 (next+e1.length+e2.length+e3.length)
    rawMat cap dem n3 ⟨rawMat,rawMat,cap,dem⟩ .r1 54 [] suffix
  let h4 := h3++e4
  have c48 : tickNatural program
      (state heap next a b c d [] (SourceRowTableProgram.encode capacity++tail1) 48)=
      some ⟨state heap next a b c d [⟨49,.r0,⟨a,b,c,d⟩⟩]
        (SourceRowTableProgram.encode capacity++tail1) 30,[],0⟩ := by rfl
  have c49 : tickNatural program (state h1 (next+e1.length) cap b c d [] tail1 49)=
      some ⟨state h1 (next+e1.length) cap b c d [⟨50,.r1,⟨cap,b,c,d⟩⟩] tail1 30,[],0⟩ := by rfl
  have c50 : tickNatural program (state h2 (next+e1.length+e2.length) cap rawMat c d [] tail2 50)=
      some ⟨state h2 (next+e1.length+e2.length) cap rawMat c d
        [⟨51,.r3,⟨cap,rawMat,c,d⟩⟩] tail2 30,[],0⟩ := by rfl
  have c51 : tickNatural program (state h3 (next+e1.length+e2.length+e3.length) cap rawMat c dem [] suffix 51)=
      some ⟨state h3 (next+e1.length+e2.length+e3.length) cap rawMat cap dem [] suffix 52,[],0⟩ := by rfl
  have c52 : tickNatural program (state h3 (next+e1.length+e2.length+e3.length) cap rawMat cap dem [] suffix 52)=
      some ⟨state h3 (next+e1.length+e2.length+e3.length) rawMat rawMat cap dem [] suffix 53,[],0⟩ := by rfl
  have c53 : tickNatural program (state h3 (next+e1.length+e2.length+e3.length) rawMat rawMat cap dem [] suffix 53)=
      some ⟨state h3 (next+e1.length+e2.length+e3.length) rawMat rawMat cap dem
        [⟨54,.r1,⟨rawMat,rawMat,cap,dem⟩⟩] suffix 46,[],0⟩ := by rfl
  have c54 : tickNatural program (state h4 (next+e1.length+e2.length+e3.length+e4.length) rawMat mat cap dem [] suffix 54)=
      some ⟨state h4 (next+e1.length+e2.length+e3.length+e4.length) cap mat cap dem [] suffix 55,[],0⟩ := by rfl
  have c55 : tickNatural program (state h4 (next+e1.length+e2.length+e3.length+e4.length) cap mat cap dem [] suffix 55)=
      some ⟨state h4 (next+e1.length+e2.length+e3.length+e4.length) cap mat mat dem [] suffix 56,[],0⟩ := by rfl
  have p1 := NaturalRun.step c48 r1
  have p2 := NaturalRun.step c49 r2
  have p3 := NaturalRun.step c50 r3
  have p4 := NaturalRun.step c51 (.step c52 (.step c53 r4))
  have p5 := NaturalRun.step c54 (.step c55 (.done _))
  have joined := run_append p1 (run_append p2 (run_append p3 (run_append p4 p5)))
  refine ⟨e1++e2++e3++e4,cap,mat,dem,?_,?_,?_,?_⟩
  · convert joined using 1 <;> simp [instructions,encode,tail1,tail2,h1,h2,h3,h4,state,
      List.append_assoc,List.map_append,Nat.add_assoc]
    omega
  · simpa [h1,h2,h3,List.append_assoc] using
      BinaryIndexedPairRead.table_extend (BinaryIndexedPairRead.table_extend
        (BinaryIndexedPairRead.table_extend hcap e2) e3) e4
  · simpa [h1,h2,h3,List.append_assoc] using hm
  · simpa [h1,h2,h3,List.append_assoc] using BinaryIndexedPairRead.table_extend hdem e4

end DirectedFlowCutGap.PackingSourceInput
