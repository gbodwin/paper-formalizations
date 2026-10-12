import DirectedFlowCutGap.OracleChoiceProgram

namespace DirectedFlowCutGap.OracleChoice
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor

theorem mask_return {heap : NaturalHeap} {a b : ℕ} {vs : List Bits} {s t : Bits}
    {es : List (Bits × Bits)} (input : GraphDiscoveryProgram.Vertices heap a vs)
    (context : OracleMask.Context heap b s t es) (next c d : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 484) (stack : List (Frame ℕ 484)) (source : Bits) :
    ∃ ext root,ext.length=OracleMask.cells s t es vs ∧
      NaturalRun program (OracleMask.steps s t es vs+2)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 150) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      BoolList (heap++ext) root (OracleMask.mask s t es vs) := by
  obtain ⟨ext,root,len,high,rep⟩ := OracleMask.mask_high
    (OracleMask.state heap next a b c d [] source 150) rfl hn rfl input context
  let frames := (⟨pc,.r3,saved⟩::stack)
  have mapped := ReferenceProgramLabels.run maskLabel OracleMask.program program mask_slots high
  have lifted := ReferenceProgramStack.run program frames mapped
  have body : NaturalRun program (OracleMask.steps s t es vs+1)
      (state heap next a b c d frames source 150) []
      (state (heap++ext) (next+ext.length) a b c root frames source 151) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,ReferenceProgramStack.state,
      OracleMask.state,maskLabel,state] using lifted
  have ret : tickNatural program (state (heap++ext) (next+ext.length) a b c root frames source 151)=
      some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,OracleMask.program,callable,state,frames,Registers.get,Registers.set]
  exact ⟨ext,root,len,by simpa [Nat.add_assoc] using run_append body (.step ret (.done _)),rep⟩

theorem capacity_return {heap : NaturalHeap} {a b : ℕ} {xs : List CapacityBottleneck.Slot}
    (input : CapacityBottleneck.Input heap a b xs) (next c d : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 484) (stack : List (Frame ℕ 484)) (source : Bits) :
    ∃ ext root,ext.length=CapacityBottleneck.selectedCells next xs ∧
      NaturalRun program (CapacityBottleneck.selectedSteps next xs+1)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 400) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      RetainedArgminProgram.Selected (heap++ext) root (RetainedArgminProgram.select (CapacityBottleneck.items next xs)) ∧
      CapacityBottleneck.Input (heap++ext) a b xs := by
  obtain ⟨out,high,rep,_,preserved,src,stk,dense,⟨ext,he,len⟩,halt⟩ := CapacityBottleneck.selected_high
    (CapacityBottleneck.state heap next a b c d [] source 240) rfl hn rfl input
  let frames := (⟨pc,.r3,saved⟩::stack)
  have mapped := ReferenceProgramLabels.run capLabel CapacityBottleneck.program program cap_slots high
  have lifted := ReferenceProgramStack.run program frames mapped
  have finish : tickNatural program (ReferenceProgramStack.state frames (ReferenceProgramLabels.state capLabel out))=
      some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c out.registers.d stack source pc,[],0⟩ := by
    simp [tickNatural,ReferenceProgramStack.state,ReferenceProgramLabels.state,cap_halt out.pc halt,
      frames,stk,src,CapacityBottleneck.state,state,Registers.get,Registers.set,dense,he,hn]
  refine ⟨ext,out.registers.d,len,?_,?_,?_⟩
  · simpa [ReferenceProgramStack.state,ReferenceProgramLabels.state,
      CapacityBottleneck.state,capLabel,state] using run_append lifted (.step finish (.done _))
  · simpa [he,CapacityBottleneck.state] using rep
  · simpa [he,CapacityBottleneck.state] using preserved

end DirectedFlowCutGap.OracleChoice
