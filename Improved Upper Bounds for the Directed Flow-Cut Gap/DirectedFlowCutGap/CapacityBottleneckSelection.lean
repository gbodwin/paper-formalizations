import DirectedFlowCutGap.CapacityCandidateConstruction

namespace DirectedFlowCutGap.CapacityBottleneck
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor RationalComparisonProgram

def selectedSteps (next : ℕ) (xs : List Slot) : ℕ :=
  steps xs+2+RetainedArgminProgram.steps (items next xs)
def selectedCells (next : ℕ) (xs : List Slot) : ℕ :=
  cells xs+RetainedArgminProgram.cells (items next xs)

theorem selected_high {xs : List Slot} (initial : NaturalState 244) (pc0 : initial.pc=240)
    (hn : initial.next=initial.heap.length) (empty : initial.stack=[])
    (input : Input initial.heap initial.registers.a initial.registers.b xs) :
    ∃ out,NaturalRun program (selectedSteps initial.next xs) initial [] out ∧
      RetainedArgminProgram.Selected out.heap out.registers.d (RetainedArgminProgram.select (items initial.next xs)) ∧
      (∃ root,RetainedArgminProgram.ItemList out.heap root (items initial.next xs)) ∧
      Input out.heap initial.registers.a initial.registers.b xs ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.next=out.heap.length ∧
      (∃ ext,out.heap=initial.heap++ext ∧ ext.length=selectedCells initial.next xs) ∧ program out.pc=.halt := by
  cases initial with
  | mk heap next regs stack pc source =>
    cases regs with
    | mk a b c d =>
      simp only at pc0 hn empty input
      subst pc;subst stack
      obtain ⟨ec,root,lc,collect,recordRep⟩ := collect_return input next c d hn ⟨a,b,c,d⟩ 241 [] source
      let h1 := heap++ec
      let n1 := next+ec.length
      have dense1 : n1=h1.length := by simp [h1,n1,hn]
      obtain ⟨u,selectRun,selected,_,src,stk,dense,⟨es,he,ls⟩,halt⟩ :=
        RetainedArgminProgram.run_high_terminal (items next xs)
          (RetainedArgminProgram.state h1 n1 root b c root [] source 178) rfl dense1 recordRep rfl
      have mapped := ReferenceProgramLabels.run label RetainedArgminProgram.program program
        (fun pc _ => slots pc) selectRun
      have selectedBody : NaturalRun program (RetainedArgminProgram.steps (items next xs))
          (state h1 n1 root b c root [] source 178) [] (ReferenceProgramLabels.state label u) := by
        simpa [ReferenceProgramLabels.state,RetainedArgminProgram.state,label,state] using mapped
      have call : tickNatural program (state heap next a b c d [] source 240)=
          some ⟨state heap next a b c d [⟨241,.r3,⟨a,b,c,d⟩⟩] source 200,[],0⟩ := by
        simp [tickNatural,program,state]
      have move : tickNatural program (state h1 n1 a b c root [] source 241)=
          some ⟨state h1 n1 root b c root [] source 178,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set]
      refine ⟨ReferenceProgramLabels.state label u,?_,selected,?_,?_,src,?_,dense,?_,?_⟩
      · have all := run_append (.step call collect) (.step move selectedBody)
        convert all using 1 <;> simp [selectedSteps,state]; omega
      · refine ⟨root,?_⟩
        change RetainedArgminProgram.ItemList u.heap root _
        rw [he]
        exact RetainedArgminProgram.list_extend recordRep es
      · change Input u.heap a b xs
        rw [he]
        exact input_extend (input_extend input ec) es
      · simp [ReferenceProgramLabels.state,stk]
      · refine ⟨ec++es,?_,?_⟩
        · simpa [ReferenceProgramLabels.state,h1,RetainedArgminProgram.state,List.append_assoc] using he
        · simp [selectedCells,lc,ls]
      · change program (label u.pc)=.halt
        rw [slots,halt];rfl

end DirectedFlowCutGap.CapacityBottleneck
