import DirectedFlowCutGap.EmptyDemandScanCall

namespace DirectedFlowCutGap.EmptyDemandScan
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor

def Valid (rows : List Bits) (e : Bits × Bits) : Prop :=
  ∃ h : value e.1<rows.length,value e.2<(rows[value e.1]).length

def result (rows : List Bits) : List (Bits × Bits) → Option (Bits × Bits)
  | [] => none
  | e::es => if EmptyDemandEdge.bit rows e.1 e.2 then some e else result rows es

def steps (rows : List Bits) : List (Bits × Bits) → ℕ
  | [] => 3
  | e::es => EmptyDemandEdge.steps e.1 e.2+
      if EmptyDemandEdge.bit rows e.1 e.2 then 9 else 11+steps rows es

def cells (rows : List Bits) : List (Bits × Bits) → ℕ
  | [] => 1
  | e::es => EmptyDemandEdge.cells e.1 e.2+1+
      if EmptyDemandEdge.bit rows e.1 e.2 then 0 else cells rows es

theorem scan_return {heap : NaturalHeap} {a b : ℕ} {ds : List (Bits × Bits)} {rows : List Bits}
    (table : Table heap a ds) (hm : GraphAdjacencyProgram.Matrix heap b rows)
    (valid : ∀ e∈ds,Valid rows e)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 160)
    (stack : List (Frame ℕ 160)) (source : Bits) :
    ∃ ext out,ext.length=cells rows ds ∧ NaturalRun program (steps rows ds)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 136) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c out stack source pc) ∧
      Result (heap++ext) out (result rows ds) := by
  induction ds generalizing heap a b next c d saved pc stack with
  | nil =>
    cases table with
    | nil hp =>
      refine ⟨[.nil],next,rfl,?_,by simp [Result,result,hn]⟩
      have t0 : tickNatural program (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 136)=
          some ⟨state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 137,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,tagBranch,hp]
      have t1 : tickNatural program (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 137)=
          some ⟨state (heap++[.nil]) (next+1) a b c next (⟨pc,.r3,saved⟩::stack) source 138,[],0⟩ := by
        simp [tickNatural,program,state,Registers.set,allocateNatural,Recipe.cell]
      have t2 : tickNatural program (state (heap++[.nil]) (next+1) a b c next (⟨pc,.r3,saved⟩::stack) source 138)=
          some ⟨state (heap++[.nil]) (next+1) saved.a saved.b saved.c next stack source pc,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set]
      exact .step t0 (.step t1 (.step t2 (.done _)))
  | cons e es ih =>
    rcases e with ⟨u,v⟩
    cases table with
    | @cons _ item tail num den _ _ _ hp he hu hv ht =>
      obtain ⟨hi,hj⟩ := valid (u,v) (by simp)
      let scratch : Cell ℕ := .pair a b
      let h0 := heap++[scratch]
      have hsc : h0[next]?=some scratch := by simp [h0,hn]
      have hp0 : h0[a]?=some (.pair item tail) := lookup_extend hp _
      have hd : EmptyDemandEdge.Demand h0 item u v :=
        ⟨num,den,lookup_extend he _,boolList_extend hu _,boolList_extend hv _⟩
      obtain ⟨e1,flag,l1,child,hflag⟩ := edge_return hd (GraphAdjacencyProgram.matrix_extend hm _) hi hj
        (next+1) next d (by simp [h0,hn]) ⟨item,b,next,d⟩ 142 (⟨pc,.r3,saved⟩::stack) source
      let h1 := h0++e1
      let n1 := next+1+e1.length
      have hn1 : n1=h1.length := by simp [n1,h1,h0,hn];omega
      have headRun : NaturalRun program (EmptyDemandEdge.steps u v+6)
          (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 136) []
          (state h1 n1 item b next flag (⟨pc,.r3,saved⟩::stack) source 142) := by
        have t0 : tickNatural program (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 136)=
            some ⟨state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 139,[],0⟩ := by
          simp [tickNatural,program,state,Registers.get,tagBranch,hp]
        have t1 : tickNatural program (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 139)=
            some ⟨state h0 (next+1) a b next d (⟨pc,.r3,saved⟩::stack) source 140,[],0⟩ := by
          simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,h0,scratch]
        have t2 : tickNatural program (state h0 (next+1) a b next d (⟨pc,.r3,saved⟩::stack) source 140)=
            some ⟨state h0 (next+1) item b next d (⟨pc,.r3,saved⟩::stack) source 141,[],0⟩ := by
          simp [tickNatural,program,state,Registers.get,Registers.set,hp0]
        have t3 : tickNatural program (state h0 (next+1) item b next d (⟨pc,.r3,saved⟩::stack) source 141)=
            some ⟨state h0 (next+1) item b next d (⟨142,.r3,⟨item,b,next,d⟩⟩::⟨pc,.r3,saved⟩::stack) source 126,[],0⟩ := by rfl
        convert NaturalRun.step t0 (.step t1 (.step t2 (.step t3 child))) using 1; simp
      cases hb : EmptyDemandEdge.bit rows u v with
      | true =>
        refine ⟨[scratch]++e1,item,?_,?_,?_⟩
        · simp [cells,hb,l1,Nat.add_comm]
        · have t0 : tickNatural program (state h1 n1 item b next flag (⟨pc,.r3,saved⟩::stack) source 142)=
              some ⟨state h1 n1 item b next flag (⟨pc,.r3,saved⟩::stack) source 143,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,tagBranch,hflag,hb,h1]
          have t1 : tickNatural program (state h1 n1 item b next flag (⟨pc,.r3,saved⟩::stack) source 143)=
              some ⟨state h1 n1 item b next item (⟨pc,.r3,saved⟩::stack) source 144,[],0⟩ := by rfl
          have t2 : tickNatural program (state h1 n1 item b next item (⟨pc,.r3,saved⟩::stack) source 144)=
              some ⟨state h1 n1 saved.a saved.b saved.c item stack source pc,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,Registers.set]
          convert run_append headRun (.step t0 (.step t1 (.step t2 (.done _)))) using 1 <;>
            simp [steps,hb,state,h1,h0,n1,List.append_assoc,Nat.add_assoc]; omega
        · have h := EmptyDemandEdge.demand_extend hd e1
          simpa [Result,result,hb,h0,List.append_assoc] using h
      | false =>
        have ht1 : Table h1 tail es := BinaryIndexedPairRead.table_extend (BinaryIndexedPairRead.table_extend ht _) _
        have hm1 : GraphAdjacencyProgram.Matrix h1 b rows := GraphAdjacencyProgram.matrix_extend (GraphAdjacencyProgram.matrix_extend hm _) _
        obtain ⟨e2,out,l2,recur,rep⟩ := ih ht1 hm1 (fun e he => valid e (List.mem_cons_of_mem _ he))
          n1 next flag hn1 ⟨tail,b,next,flag⟩ 149 (⟨pc,.r3,saved⟩::stack)
        refine ⟨[scratch]++e1++e2,out,?_,?_,?_⟩
        · simp [cells,hb,l1,l2];omega
        · have hp1 : h1[a]?=some (.pair item tail) := lookup_extend hp0 _
          have hsc1 : h1[next]?=some scratch := lookup_extend hsc _
          have t0 : tickNatural program (state h1 n1 item b next flag (⟨pc,.r3,saved⟩::stack) source 142)=
              some ⟨state h1 n1 item b next flag (⟨pc,.r3,saved⟩::stack) source 146,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,tagBranch,hflag,hb,h1]
          have t1 : tickNatural program (state h1 n1 item b next flag (⟨pc,.r3,saved⟩::stack) source 146)=
              some ⟨state h1 n1 a b next flag (⟨pc,.r3,saved⟩::stack) source 147,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,Registers.set,hsc1,scratch]
          have t2 : tickNatural program (state h1 n1 a b next flag (⟨pc,.r3,saved⟩::stack) source 147)=
              some ⟨state h1 n1 tail b next flag (⟨pc,.r3,saved⟩::stack) source 148,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,Registers.set,hp1]
          have t3 : tickNatural program (state h1 n1 tail b next flag (⟨pc,.r3,saved⟩::stack) source 148)=
              some ⟨state h1 n1 tail b next flag (⟨149,.r3,⟨tail,b,next,flag⟩⟩::⟨pc,.r3,saved⟩::stack) source 136,[],0⟩ := by rfl
          have t4 : tickNatural program (state (h1++e2) (n1+e2.length) tail b next out (⟨pc,.r3,saved⟩::stack) source 149)=
              some ⟨state (h1++e2) (n1+e2.length) saved.a saved.b saved.c out stack source pc,[],0⟩ := by
            simp [tickNatural,program,state,Registers.get,Registers.set]
          have last := run_append recur (.step t4 (.done _))
          have whole := run_append headRun (.step t0 (.step t1 (.step t2 (.step t3 last))))
          convert whole using 1 <;> simp [steps,hb,state,h1,h0,n1,List.append_assoc,Nat.add_assoc] <;> omega
        · simpa [Result,result,hb,h1,h0,List.append_assoc] using rep
end DirectedFlowCutGap.EmptyDemandScan
