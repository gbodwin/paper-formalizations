import DirectedFlowCutGap.OriginalDispatchPrefix

namespace DirectedFlowCutGap.OriginalDispatch
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor

def activeResult (vs : List Bits) (cs : List (Bits × Bits)) (rows : List Bits) (ds : List (Bits × Bits)) : Value :=
  match AvoidingDemandScan.result vs cs rows ds with
  | some w => .positive w
  | none => .zero (PackingZeroMask.mask cs)

def activeSteps (vs : List Bits) (cs : List (Bits × Bits)) (rows : List Bits) (ds : List (Bits × Bits)) : ℕ :=
  AvoidingDemandScan.steps vs cs rows ds+
    match AvoidingDemandScan.result vs cs rows ds with
    | some _ => 8
    | none => PackingZeroMask.steps cs+13

def activeCells (vs : List Bits) (cs : List (Bits × Bits)) (rows : List Bits) (ds : List (Bits × Bits)) : ℕ :=
  AvoidingDemandScan.cells vs cs rows ds+2+
    match AvoidingDemandScan.result vs cs rows ds with
    | some _ => 0
    | none => 2*cs.length+1

theorem active_return {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n) (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (ds : List (Fin n × Fin n)) {heap : NaturalHeap} {a b c : ℕ}
    (table : Table heap a (ds.map fun e => (label e.1,label e.2)))
    (context : Context heap b (List.ofFn label) (IndexedRationalRead.fields costs.toList)
      (GraphRelaxationRefinement.matrix adjacency)) (scratch : heap[c]?=some (.pair a b))
    (next oldB d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 2140)
    (stack : List (Frame ℕ 2140)) (source : Bits) :
    ∃ ext out,ext.length=activeCells (List.ofFn label) (IndexedRationalRead.fields costs.toList)
      (GraphRelaxationRefinement.matrix adjacency) (ds.map fun e => (label e.1,label e.2)) ∧
      NaturalRun program (activeSteps (List.ofFn label) (IndexedRationalRead.fields costs.toList)
        (GraphRelaxationRefinement.matrix adjacency) (ds.map fun e => (label e.1,label e.2)))
        (state heap next a oldB c d (⟨pc,.r3,saved⟩::stack) source 2120) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c out stack source pc) ∧
      Result (heap++ext) out (activeResult (List.ofFn label) (IndexedRationalRead.fields costs.toList)
        (GraphRelaxationRefinement.matrix adjacency) (ds.map fun e => (label e.1,label e.2))) := by
  let frames : List (Frame ℕ 2140) := ⟨pc,.r3,saved⟩::stack
  obtain ⟨e1,path,l1,child,rep⟩ := scan_return adjacency costs label hlabel ds table context
    next c d hn ⟨a,b,c,d⟩ 2122 frames source
  have t1 : tickNatural program (state heap next a oldB c d frames source 2120)=
      some ⟨state heap next a b c d frames source 2121,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,scratch]
  have t2 : tickNatural program (state heap next a b c d frames source 2121)=
      some ⟨state heap next a b c d (⟨2122,.r3,⟨a,b,c,d⟩⟩::frames) source 2090,[],0⟩ := rfl
  have before := NaturalRun.step t1 (.step t2 child)
  let h1 : NaturalHeap := heap++e1
  let n1 := next+e1.length
  have hn1 : n1=h1.length := by simp [n1,h1,hn]
  cases hr : AvoidingDemandScan.result (List.ofFn label) (IndexedRationalRead.fields costs.toList)
      (GraphRelaxationRefinement.matrix adjacency) (ds.map fun e => (label e.1,label e.2)) with
  | some w =>
    have rwit : AvoidingDemandScan.Result h1 path (some w) := by rw [hr] at rep;exact rep
    obtain ⟨er,wr,hp,he,hw⟩ := rwit
    have branch : tickNatural program (state h1 n1 a b c path frames source 2122)=
        some ⟨state h1 n1 a b c path frames source 2123,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,tagBranch,hp]
    have finish := tag_return none h1 n1 a b c path saved pc stack source
    have whole := run_append before (.step branch finish)
    let extra : NaturalHeap := [tagCell none,.pair n1 path]
    refine ⟨e1++extra,n1+1,?_,?_,?_⟩
    · simp [activeCells,hr,extra,l1]
    · convert whole using 1 <;> simp [activeSteps,hr,extra,state,h1,n1,List.append_assoc,Nat.add_assoc]
    · simp only [activeResult,hr,Result]
      refine ⟨n1,path,?_,?_,?_⟩
      · have h : (h1++extra)[n1+1]?=some (.pair n1 path) := by simp [extra,hn1]
        simpa only [h1,List.append_assoc] using h
      · have h : (h1++extra)[n1]?=some .nil := by simp [extra,hn1,tagCell]
        simpa only [h1,List.append_assoc] using h
      · obtain ⟨e,w⟩ := w
        have represented : AvoidingDemandScan.Result (h1++extra) path (some (e,w)) :=
          ⟨er,wr,lookup_extend hp extra,EmptyDemandEdge.demand_extend he extra,
            GraphWalkExtension.walk_extend hw extra⟩
        simpa only [h1,List.append_assoc] using represented
  | none =>
    have hnil : h1[path]?=some .nil := by rw [hr] at rep;exact rep
    obtain ⟨vr,detail,cr,ar,hp,hd,hv,hc,ha⟩ := AvoidingDemandScan.context_extend context e1
    obtain ⟨e2,mask,l2,zero,maskRep⟩ := zero_return hc n1 b c path hn1 ⟨cr,b,c,path⟩ 2128 frames source
    have branch : tickNatural program (state h1 n1 a b c path frames source 2122)=
        some ⟨state h1 n1 a b c path frames source 2125,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,tagBranch,hnil]
    have t3 : tickNatural program (state h1 n1 a b c path frames source 2125)=
        some ⟨state h1 n1 detail b c path frames source 2126,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,hp,h1]
    have t4 : tickNatural program (state h1 n1 detail b c path frames source 2126)=
        some ⟨state h1 n1 cr b c path frames source 2127,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,hd,h1]
    have t5 : tickNatural program (state h1 n1 cr b c path frames source 2127)=
        some ⟨state h1 n1 cr b c path (⟨2128,.r3,⟨cr,b,c,path⟩⟩::frames) source 190,[],0⟩ := rfl
    let h2 := h1++e2
    let n2 := n1+e2.length
    have hn2 : n2=h2.length := by simp [n2,h2,hn1]
    have finish := tag_return (some true) h2 n2 cr b c mask saved pc stack source
    have last := run_append zero finish
    have whole := run_append before (.step branch (.step t3 (.step t4 (.step t5 last))))
    let extra : NaturalHeap := [tagCell (some true),.pair n2 mask]
    refine ⟨e1++e2++extra,n2+1,?_,?_,?_⟩
    · simp [activeCells,hr,extra,l1,l2,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    · convert whole using 1 <;> simp [activeSteps,hr,extra,state,h1,n1,h2,n2,List.append_assoc,Nat.add_assoc]
      exact Nat.add_left_comm (PackingZeroMask.steps (IndexedRationalRead.fields costs.toList)) 4 9
    · simp only [activeResult,hr,Result]
      refine ⟨n2,mask,?_,?_,?_⟩
      · have h : (h2++extra)[n2+1]?=some (.pair n2 mask) := by simp [extra,hn2]
        simpa only [h2,h1,List.append_assoc] using h
      · have h : (h2++extra)[n2]?=some (.flag true) := by simp [extra,hn2,tagCell]
        simpa only [h2,h1,List.append_assoc] using h
      · simpa only [h2,h1,List.append_assoc] using boolList_extend maskRep extra
end DirectedFlowCutGap.OriginalDispatch
