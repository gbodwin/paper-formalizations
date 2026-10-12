import DirectedFlowCutGap.GraphOracleDemandCall

namespace DirectedFlowCutGap.GraphOracleMachine
open BinaryArithmetic BinaryRational BinaryFractionalRows ImmutableReferenceSimulation ImmutableReferenceTerminal
open BooleanTableRead PackedBooleanConstructor

theorem choice_return {n : ℕ} (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (capacity : Row n) (hn : 0<n) {heap : NaturalHeap} {a b : ℕ}
    {q : Option (BinaryFractionalGraphOracle.Selected n)}
    (selected : DemandCollection.SelectedOrigin heap a label q)
    (context : CapacityBottleneck.GraphContext heap b label capacity)
    (next c d : ℕ) (dense : next=heap.length) (saved : Registers ℕ) (pc : Fin 2120)
    (stack : List (Frame ℕ 2120)) (source : Bits) :
    ∃ steps ext root,NaturalRun program steps
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 2084) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      OracleChoice.StoredChoice (heap++ext) root label (OracleChoice.choice capacity hn q) ∧
      ∀ W,(∀ i,(label i).length≤W) →
        (∀ i,(get capacity i).num.length≤W ∧ (get capacity i).den.length≤W) →
        steps ≤ OracleChoice.instructionBound q W+2 := by
  obtain ⟨steps,ext,root,high,stored,bound⟩ := OracleChoice.choice_high label hlabel capacity hn
    (OracleChoice.state heap next a b c d [] source 480) rfl dense rfl selected context
  let frames := (⟨pc,.r3,saved⟩::stack)
  have mapped := ReferenceProgramLabels.run choiceLabel OracleChoice.program program choice_slots high
  have lifted := ReferenceProgramStack.run program frames mapped
  have body : NaturalRun program steps (state heap next a b c d frames source 2084) []
      (state (heap++ext) (next+ext.length) a b c root frames source 2085) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,ReferenceProgramStack.state,
      OracleChoice.state,choiceLabel,state] using lifted
  have ret : tickNatural program (state (heap++ext) (next+ext.length) a b c root frames source 2085)=
      some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc,[],0⟩ := by
    simp [tickNatural,program,OracleChoice.program,callable,state,frames,Registers.get,Registers.set]
  refine ⟨steps+1,ext,root,by simpa using run_append body (.step ret (.done _)),stored,?_⟩
  intro W labels capacities
  have h := bound W labels capacities
  omega

end DirectedFlowCutGap.GraphOracleMachine
