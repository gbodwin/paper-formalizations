import DirectedFlowCutGap.AvoidingDemandScanHead

namespace DirectedFlowCutGap.AvoidingDemandScan
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor
open IntegralNetworkFlow IntegralNetworkFlow.Tabulated

def result (vs : List Bits) (costs : List (Bits × Bits)) (rows : List Bits) :
    List (Bits × Bits) → Option ((Bits × Bits) × GraphWalkExtension.Walk)
  | [] => none
  | e::es => match AvoidingKeptPath.result e.1 e.2 vs costs rows with
    | none => result vs costs rows es
    | some w => some (e,w)

def steps (vs : List Bits) (costs : List (Bits × Bits)) (rows : List Bits) : List (Bits × Bits) → ℕ
  | [] => 3
  | e::es => AvoidingKeptPath.steps e.1 e.2 vs costs rows+
      match AvoidingKeptPath.result e.1 e.2 vs costs rows with
      | none => 20+steps vs costs rows es
      | some _ => 19

def cells (vs : List Bits) (costs : List (Bits × Bits)) (rows : List Bits) : List (Bits × Bits) → ℕ
  | [] => 1
  | e::es => AvoidingKeptPath.cells e.1 e.2 vs costs rows+3+
      match AvoidingKeptPath.result e.1 e.2 vs costs rows with
      | none => cells vs costs rows es
      | some _ => 1

theorem scan_return {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n) (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (ds : List (Fin n × Fin n)) {heap : NaturalHeap} {a b : ℕ}
    (table : Table heap a (ds.map fun e => (label e.1,label e.2)))
    (context : Context heap b (List.ofFn label) (IndexedRationalRead.fields costs.toList)
      (GraphRelaxationRefinement.matrix adjacency))
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 1900)
    (stack : List (Frame ℕ 1900)) (source : Bits) :
    ∃ ext out,ext.length=cells (List.ofFn label) (IndexedRationalRead.fields costs.toList)
      (GraphRelaxationRefinement.matrix adjacency) (ds.map fun e => (label e.1,label e.2)) ∧
      NaturalRun program (steps (List.ofFn label) (IndexedRationalRead.fields costs.toList)
        (GraphRelaxationRefinement.matrix adjacency) (ds.map fun e => (label e.1,label e.2)))
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 1810) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c out stack source pc) ∧
      Result (heap++ext) out (result (List.ofFn label) (IndexedRationalRead.fields costs.toList)
        (GraphRelaxationRefinement.matrix adjacency) (ds.map fun e => (label e.1,label e.2))) := by
  induction ds generalizing heap a b next c d saved pc stack with
  | nil =>
    cases table with
    | nil hp =>
      refine ⟨[.nil],next,rfl,?_,by simp [Result,result,hn]⟩
      have t0 : tickNatural program (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 1810)=
          some ⟨state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 1811,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,tagBranch,hp]
      have t1 : tickNatural program (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 1811)=
          some ⟨state (heap++[.nil]) (next+1) a b c next (⟨pc,.r3,saved⟩::stack) source 1812,[],0⟩ := by
        simp [tickNatural,program,state,Registers.set,allocateNatural,Recipe.cell]
      have t2 : tickNatural program (state (heap++[.nil]) (next+1) a b c next (⟨pc,.r3,saved⟩::stack) source 1812)=
          some ⟨state (heap++[.nil]) (next+1) saved.a saved.b saved.c next stack source pc,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set]
      exact .step t0 (.step t1 (.step t2 (.done _)))
  | cons e es ih =>
    rcases e with ⟨s,t⟩
    cases table with
    | @cons _ item tail sr tr _ _ _ hp he hs ht htail =>
      have demand : EmptyDemandEdge.Demand heap item (label s) (label t) := ⟨sr,tr,he,hs,ht⟩
      obtain ⟨e1,path,vr,l1,headRun,pathRep,scratch⟩ := head_query adjacency costs s t label hlabel hp demand context
        next c d hn (⟨pc,.r3,saved⟩::stack) source
      let h1 := heap++e1
      let n1 := next+e1.length
      have hn1 : n1=h1.length := by simp [n1,h1,hn]
      have t0 : tickNatural program (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 1810)=
          some ⟨state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 1813,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,tagBranch,hp]
      have first := NaturalRun.step t0 headRun
      have hp1 : h1[a]?=some (.pair item tail) := lookup_extend hp e1
      cases hr : AvoidingKeptPath.result (label s) (label t) (List.ofFn label)
          (IndexedRationalRead.fields costs.toList) (GraphRelaxationRefinement.matrix adjacency) with
      | none =>
        have hnil : h1[path]?=some .nil := by rw [hr] at pathRep;exact pathRep
        obtain ⟨e2,out,l2,recur,rep⟩ := ih (BinaryIndexedPairRead.table_extend htail e1)
          (context_extend context e1) n1 next path hn1 ⟨tail,b,next,path⟩ 1838 (⟨pc,.r3,saved⟩::stack)
        have t1 : tickNatural program (state h1 n1 vr (next+2) next path (⟨pc,.r3,saved⟩::stack) source 1824)=
            some ⟨state h1 n1 vr (next+2) next path (⟨pc,.r3,saved⟩::stack) source 1834,[],0⟩ := by
          simp [tickNatural,program,state,Registers.get,tagBranch,hnil]
        have t2 : tickNatural program (state h1 n1 vr (next+2) next path (⟨pc,.r3,saved⟩::stack) source 1834)=
            some ⟨state h1 n1 a (next+2) next path (⟨pc,.r3,saved⟩::stack) source 1835,[],0⟩ := by
          simp [tickNatural,program,state,Registers.get,Registers.set,scratch,h1]
        have t3 : tickNatural program (state h1 n1 a (next+2) next path (⟨pc,.r3,saved⟩::stack) source 1835)=
            some ⟨state h1 n1 tail (next+2) next path (⟨pc,.r3,saved⟩::stack) source 1836,[],0⟩ := by
          simp [tickNatural,program,state,Registers.get,Registers.set,hp1]
        have t4 : tickNatural program (state h1 n1 tail (next+2) next path (⟨pc,.r3,saved⟩::stack) source 1836)=
            some ⟨state h1 n1 tail b next path (⟨pc,.r3,saved⟩::stack) source 1837,[],0⟩ := by
          simp [tickNatural,program,state,Registers.get,Registers.set,scratch,h1]
        have t5 : tickNatural program (state h1 n1 tail b next path (⟨pc,.r3,saved⟩::stack) source 1837)=
            some ⟨state h1 n1 tail b next path (⟨1838,.r3,⟨tail,b,next,path⟩⟩::⟨pc,.r3,saved⟩::stack) source 1810,[],0⟩ := rfl
        have t6 : tickNatural program (state (h1++e2) (n1+e2.length) tail b next out (⟨pc,.r3,saved⟩::stack) source 1838)=
            some ⟨state (h1++e2) (n1+e2.length) saved.a saved.b saved.c out stack source pc,[],0⟩ := by
          simp [tickNatural,program,state,Registers.get,Registers.set]
        have last := run_append recur (.step t6 (.done _))
        have whole := run_append first (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 last)))))
        refine ⟨e1++e2,out,?_,?_,?_⟩
        · simp [cells,hr,l1,l2]
        · convert whole using 1 <;>
            simp [steps,hr,state,h1,n1,List.append_assoc,Nat.add_comm,Nat.add_left_comm]
          all_goals omega
        · simpa only [List.map_cons,result,hr,h1,List.append_assoc] using rep
      | some w =>
        have hw : GraphWalkExtension.StoredWalk h1 path w := by rw [hr] at pathRep;exact pathRep
        obtain ⟨edges,cr,hpath,hedges,hcost⟩ := hw
        let selected : Cell ℕ := .pair item path
        have t1 : tickNatural program (state h1 n1 vr (next+2) next path (⟨pc,.r3,saved⟩::stack) source 1824)=
            some ⟨state h1 n1 vr (next+2) next path (⟨pc,.r3,saved⟩::stack) source 1825,[],0⟩ := by
          simp [tickNatural,program,state,Registers.get,tagBranch,hpath]
        have t2 : tickNatural program (state h1 n1 vr (next+2) next path (⟨pc,.r3,saved⟩::stack) source 1825)=
            some ⟨state h1 n1 a (next+2) next path (⟨pc,.r3,saved⟩::stack) source 1826,[],0⟩ := by
          simp [tickNatural,program,state,Registers.get,Registers.set,scratch,h1]
        have t3 : tickNatural program (state h1 n1 a (next+2) next path (⟨pc,.r3,saved⟩::stack) source 1826)=
            some ⟨state h1 n1 item (next+2) next path (⟨pc,.r3,saved⟩::stack) source 1827,[],0⟩ := by
          simp [tickNatural,program,state,Registers.get,Registers.set,hp1]
        have t4 : tickNatural program (state h1 n1 item (next+2) next path (⟨pc,.r3,saved⟩::stack) source 1827)=
            some ⟨state (h1++[selected]) (n1+1) item (next+2) next n1 (⟨pc,.r3,saved⟩::stack) source 1828,[],0⟩ := by
          simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,selected]
        have t5 : tickNatural program (state (h1++[selected]) (n1+1) item (next+2) next n1 (⟨pc,.r3,saved⟩::stack) source 1828)=
            some ⟨state (h1++[selected]) (n1+1) saved.a saved.b saved.c n1 stack source pc,[],0⟩ := by
          simp [tickNatural,program,state,Registers.get,Registers.set]
        have whole := run_append first (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.done _))))))
        refine ⟨e1++[selected],n1,?_,?_,?_⟩
        · simp [cells,hr,l1]
        · convert whole using 1 <;>
            simp [steps,hr,state,h1,n1,List.append_assoc,Nat.add_comm,Nat.add_left_comm]
          all_goals omega
        · simp only [List.map_cons,result,hr,Result]
          refine ⟨item,path,?_,?_,?_⟩
          · have hout : (h1++[selected])[n1]?=some selected := by simp [hn1]
            simpa only [h1,List.append_assoc] using hout
          · exact EmptyDemandEdge.demand_extend demand _
          · change GraphWalkExtension.StoredWalk _ _ _
            simpa only [h1,List.append_assoc] using GraphWalkExtension.walk_extend ⟨edges,cr,hpath,hedges,hcost⟩ [selected]
end DirectedFlowCutGap.AvoidingDemandScan
