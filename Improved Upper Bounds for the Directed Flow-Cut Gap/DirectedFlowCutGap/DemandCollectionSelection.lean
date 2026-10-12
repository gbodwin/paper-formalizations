import DirectedFlowCutGap.DemandCollectionExecution

/-! The candidate selector reads exactly the record list allocated by demand
traversal and actual shortest-path queries. No path or cost list is supplied. -/
namespace DirectedFlowCutGap.DemandCollection
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor GraphWalkExtension

def selectedSteps (vs adjacency : List Bits) (rows : List Fraction) (next : ℕ) (xs : List Demand) : ℕ :=
  steps vs adjacency rows xs+2+RetainedArgminProgram.steps ((records vs adjacency rows next xs).map Record.item)

def selectedCells (vs adjacency : List Bits) (rows : List Fraction) (next : ℕ) (xs : List Demand) : ℕ :=
  cells vs adjacency rows xs+RetainedArgminProgram.cells ((records vs adjacency rows next xs).map Record.item)

theorem selected_high {xs : List Demand} {vs adjacency : List Bits} {values : List Fraction}
    (N : ℕ) (initial : NaturalState 1604) (pc0 : initial.pc=1600)
    (hn : initial.next=initial.heap.length) (empty : initial.stack=[])
    (input : DemandList initial.heap initial.registers.a xs)
    (shared : Shared initial.heap initial.registers.b vs adjacency values)
    (rows : N ≤ adjacency.length)
    (cols : ∀ (i : ℕ) (hi : i<N),N ≤ (adjacency[i]'(lt_of_lt_of_le hi rows)).length)
    (hv : ∀ v∈vs,value v<N) (hc : ∀ v∈vs,value v<values.length)
    (valid : ∀ x∈xs,value x.targetWord<N ∧
      ∀ q,GraphDiscoveryProgram.minimize vs adjacency values x.sourceWord x.targetWord x.sourceWord=some q →
        ∀ w∈(CostedSupportProgram.edges vs adjacency q.edges x.sourceWord x.targetWord).map Prod.fst,value w<values.length) :
    ∃ out,NaturalRun program (selectedSteps vs adjacency values initial.next xs) initial [] out ∧
      RetainedArgminProgram.Selected out.heap out.registers.d
        (RetainedArgminProgram.select ((records vs adjacency values initial.next xs).map Record.item)) ∧
      (∃ root,RecordList out.heap root (records vs adjacency values initial.next xs)) ∧
      DemandList out.heap initial.registers.a xs ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.next=out.heap.length ∧
      (∃ ext,out.heap=initial.heap++ext ∧ ext.length=selectedCells vs adjacency values initial.next xs) ∧
      program out.pc=.halt := by
  cases initial with
  | mk heap next regs stack pc source =>
    cases regs with
    | mk a b c d =>
      simp only at pc0 hn empty input shared
      subst pc;subst stack
      obtain ⟨ec,root,lc,collect,recordRep⟩ := collect_return N input rows cols hv hc valid
        next b c d hn shared ⟨a,b,c,d⟩ 1601 [] source
      let h1 := heap++ec
      let n1 := next+ec.length
      have dense1 : n1=h1.length := by simp [h1,n1,hn]
      obtain ⟨u,selectRun,selected,_,src,stk,dense,⟨es,he,ls⟩,halt⟩ :=
        RetainedArgminProgram.run_high_terminal ((records vs adjacency values next xs).map Record.item)
          (RetainedArgminProgram.state h1 n1 root b c root [] source 178) rfl dense1 (item_list recordRep) rfl
      have mapped := ReferenceProgramLabels.run selectLabel RetainedArgminProgram.program program
        (fun pc _ => select_slots pc) selectRun
      have selectedBody : NaturalRun program (RetainedArgminProgram.steps ((records vs adjacency values next xs).map Record.item))
          (state h1 n1 root b c root [] source 1522) [] (ReferenceProgramLabels.state selectLabel u) := by
        simpa [ReferenceProgramLabels.state,RetainedArgminProgram.state,selectLabel,state] using mapped
      have call : tickNatural program (state heap next a b c d [] source 1600)=
          some ⟨state heap next a b c d [⟨1601,.r3,⟨a,b,c,d⟩⟩] source 1540,[],0⟩ := by
        simp [tickNatural,program,state]
      have move : tickNatural program (state h1 n1 a b c root [] source 1601)=
          some ⟨state h1 n1 root b c root [] source 1522,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set]
      refine ⟨ReferenceProgramLabels.state selectLabel u,?_,selected,?_,?_,src,?_,dense,?_,?_⟩
      · have all := run_append (.step call collect) (.step move selectedBody)
        convert all using 1 <;> simp [selectedSteps,state]; omega
      · refine ⟨root,?_⟩
        change RecordList u.heap root _
        rw [he]
        exact records_extend recordRep es
      · change DemandList u.heap a xs
        rw [he]
        exact demands_extend (demands_extend input ec) es
      · simp [ReferenceProgramLabels.state,stk]
      · refine ⟨ec++es,?_,?_⟩
        · simpa [ReferenceProgramLabels.state,h1,RetainedArgminProgram.state,List.append_assoc] using he
        · simp [selectedCells,lc,ls]
      · change program (selectLabel u.pc)=.halt
        rw [select_slots,halt];rfl

end DirectedFlowCutGap.DemandCollection
