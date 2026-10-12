import DirectedFlowCutGap.GraphRoundData

/-! Real initial-table allocation and pass-context construction for successive
rounds. All outputs remain in the same append-only heap. -/
namespace DirectedFlowCutGap.GraphDiscoveryProgram
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor GraphWalkExtension

theorem initial_table {heap : NaturalHeap} {b tr bundle : ℕ} {target : Bits}
    (hp : heap[b]?=some (.pair tr bundle)) (ht : BoolList heap tr target)
    (next a c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 720)
    (stack : List (Frame ℕ 720)) (source : Bits) :
    ∃ ext root,ext.length=8 ∧ NaturalRun program 12
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 661) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Table (heap++ext) root [(target,zero)] := by
  let frames := (⟨pc,.r3,saved⟩::stack)
  obtain ⟨ez,rz,lz,runZ,repZ⟩ := zero_return heap next a b c d hn ⟨a,b,c,d⟩ 662 frames source
  let h0 := heap++ez
  let n0 := next+ez.length
  let e0 : NaturalHeap := [.pair tr rz,.nil,.pair n0 (n0+1)]
  have dense : n0=h0.length := by simp [h0,n0,hn]
  have t661 : tickNatural program (state heap next a b c d frames source 661)=
      some ⟨state heap next a b c d (⟨662,.r3,⟨a,b,c,d⟩⟩::frames) source 590,[],0⟩ := by
    simp [tickNatural,program,state]
  have t662 : tickNatural program (state h0 n0 a b c rz frames source 662)=
      some ⟨state h0 n0 tr b c rz frames source 663,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,h0,lookup_extend hp ez]
  have t663 : tickNatural program (state h0 n0 tr b c rz frames source 663)=
      some ⟨state (h0++[.pair tr rz]) (n0+1) n0 b c rz frames source 664,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell]
  have t664 : tickNatural program (state (h0++[.pair tr rz]) (n0+1) n0 b c rz frames source 664)=
      some ⟨state (h0++[.pair tr rz,.nil]) (n0+2) n0 b c (n0+1) frames source 665,[],0⟩ := by
    simp [tickNatural,program,state,Registers.set,allocateNatural,Recipe.cell,List.append_assoc]
  have t665 : tickNatural program (state (h0++[.pair tr rz,.nil]) (n0+2) n0 b c (n0+1) frames source 665)=
      some ⟨state (h0++e0) (n0+3) n0 b c (n0+2) frames source 666,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,List.append_assoc,e0]
  have t666 : tickNatural program (state (h0++e0) (n0+3) n0 b c (n0+2) frames source 666)=
      some ⟨state (h0++e0) (n0+3) saved.a saved.b saved.c (n0+2) stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,frames,Registers.get,Registers.set]
  have rep : Table (h0++e0) (n0+2) [(target,zero)] :=
    .cons (head:=n0) (tail:=n0+1) (by simp [e0,dense])
      ⟨tr,rz,by simp [e0,dense],boolList_extend (boolList_extend ht ez) e0,walk_extend repZ e0⟩
      (.nil (by simp [e0,dense]))
  refine ⟨ez++e0,n0+2,by simp [e0,lz],?_,?_⟩
  · have last := NaturalRun.step t662 (.step t663 (.step t664 (.step t665 (.step t666 (.done _)))))
    convert NaturalRun.step t661 (run_append runZ last) using 1 <;>
      simp [h0,n0,e0,List.append_assoc,Nat.add_assoc]
  · simpa [h0,List.append_assoc] using rep

/-- The new table returned by the previous real round is installed in the
actual two-cell context passed to this round's real enumeration traversal. -/
theorem next_pass {heap : NaturalHeap} {b root : ℕ} {vertices adjacency : List Bits}
    {rows : List Fraction} {sw target : Bits} {old : List Entry}
    (context : GlobalContext heap b vertices adjacency rows sw target) (table : Table heap root old)
    (hi : ∀ u∈vertices,value u<adjacency.length) (hc : ∀ u∈vertices,value u<rows.length)
    (hcols : ∀ u,(hu : u∈vertices) → ∀ x∈old,value x.1<(adjacency[value u]'(hi u hu)).length)
    (next a c : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 720)
    (stack : List (Frame ℕ 720)) (source : Bits) :
    ∃ ext out,ext.length=2+passCells adjacency rows sw target old vertices ∧
      NaturalRun program (passSteps adjacency rows sw target old vertices+8)
        (state heap next a b c root (⟨pc,.r3,saved⟩::stack) source 672) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c out stack source pc) ∧
      Table (heap++ext) out (pass adjacency rows sw target old vertices) := by
  obtain ⟨tr,bundle,enumRoot,mix,matrix,cost,hp,hb,hm,ht,he,ha,hcost⟩ := context
  let frames := (⟨pc,.r3,saved⟩::stack)
  let e0 : NaturalHeap := [.pair root mix,.pair tr next]
  let h0 := heap++e0
  let n0 := next+2
  have dense : n0=h0.length := by simp [h0,n0,e0,hn]
  have ctx : Context h0 (next+1) adjacency rows sw target old :=
    ⟨tr,next,root,mix,matrix,cost,by simp [h0,e0,hn],by simp [h0,e0,hn],lookup_extend hm e0,
      boolList_extend ht e0,GraphRelaxationProgram.table_extend table e0,
      GraphAdjacencyProgram.matrix_extend ha e0,PathCostMaterialization.context_extend hcost e0⟩
  obtain ⟨ext,out,len,body,rep⟩ := pass_return (vertices_extend he e0) ctx hi hc hcols
    n0 next root dense ⟨enumRoot,next+1,next,root⟩ 679 frames source
  have t672 : tickNatural program (state heap next a b c root frames source 672)=
      some ⟨state heap next a b bundle root frames source 673,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hp]
  have t673 : tickNatural program (state heap next a b bundle root frames source 673)=
      some ⟨state heap next enumRoot b bundle root frames source 674,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hb]
  have t674 : tickNatural program (state heap next enumRoot b bundle root frames source 674)=
      some ⟨state heap next enumRoot b mix root frames source 675,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hb]
  have t675 : tickNatural program (state heap next enumRoot b mix root frames source 675)=
      some ⟨state (heap++[.pair root mix]) (next+1) enumRoot b next root frames source 676,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell]
  have t676 : tickNatural program (state (heap++[.pair root mix]) (next+1) enumRoot b next root frames source 676)=
      some ⟨state (heap++[.pair root mix]) (next+1) enumRoot tr next root frames source 677,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,lookup_extend hp [.pair root mix]]
  have t677 : tickNatural program (state (heap++[.pair root mix]) (next+1) enumRoot tr next root frames source 677)=
      some ⟨state h0 n0 enumRoot (next+1) next root frames source 678,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,h0,n0,e0,List.append_assoc]
  have t678 : tickNatural program (state h0 n0 enumRoot (next+1) next root frames source 678)=
      some ⟨state h0 n0 enumRoot (next+1) next root (⟨679,.r3,⟨enumRoot,next+1,next,root⟩⟩::frames) source 630,[],0⟩ := by
    simp [tickNatural,program,state]
  have t679 : tickNatural program (state (h0++ext) (n0+ext.length) enumRoot (next+1) next out frames source 679)=
      some ⟨state (h0++ext) (n0+ext.length) saved.a saved.b saved.c out stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,frames,Registers.get,Registers.set]
  refine ⟨e0++ext,out,by simp [e0,len]; omega,?_,?_⟩
  · have joined := NaturalRun.step t672 (.step t673 (.step t674 (.step t675 (.step t676
      (.step t677 (.step t678 (run_append body (.step t679 (.done _)))))))))
    convert joined using 1 <;> simp [h0,n0,e0,List.append_assoc,Nat.add_assoc]
    congr 1
    omega
  · simpa [h0,List.append_assoc] using rep

end DirectedFlowCutGap.GraphDiscoveryProgram
