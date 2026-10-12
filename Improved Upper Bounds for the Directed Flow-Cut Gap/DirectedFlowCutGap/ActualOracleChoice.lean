import DirectedFlowCutGap.OracleChoiceExecution

namespace DirectedFlowCutGap.OracleChoice
open BinaryArithmetic BinaryRational BinaryFractionalRows ImmutableReferenceSimulation ImmutableReferenceTerminal
open BooleanTableRead PackedBooleanConstructor

theorem choice_high {n : ℕ} (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (capacity : Row n) (hn : 0<n) (initial : NaturalState 484) (pc0 : initial.pc=480)
    (dense : initial.next=initial.heap.length) (empty : initial.stack=[])
    {q : Option (BinaryFractionalGraphOracle.Selected n)}
    (selected : DemandCollection.SelectedOrigin initial.heap initial.registers.a label q)
    (context : CapacityBottleneck.GraphContext initial.heap initial.registers.b label capacity) :
    ∃ steps ext root,NaturalRun program steps initial []
      (state (initial.heap++ext) (initial.next+ext.length) initial.registers.a initial.registers.b
        initial.registers.c root [] initial.source 481) ∧
      StoredChoice (initial.heap++ext) root label (choice capacity hn q) ∧
      ∀ W,(∀ i,(label i).length≤W) →
        (∀ i,(get capacity i).num.length≤W ∧ (get capacity i).den.length≤W) →
        steps ≤ instructionBound q W+1 := by
  cases initial with
  | mk heap next regs stack pc source =>
    cases regs with
    | mk a b c d =>
      simp only at pc0 dense empty selected context
      subst pc;subst stack
      obtain ⟨steps,ext,root,body,stored,bound⟩ := choice_return label hlabel capacity hn selected context
        next c d dense ⟨a,b,c,d⟩ 481 [] source
      have first : tickNatural program (state heap next a b c d [] source 480)=
          some ⟨state heap next a b c d [⟨481,.r3,⟨a,b,c,d⟩⟩] source 410,[],0⟩ := by
        simp [tickNatural,program,state]
      refine ⟨steps+1,ext,root,?_,stored,?_⟩
      · simpa [state,Nat.add_comm] using NaturalRun.step first body
      · intro W labels capacities
        exact Nat.add_le_add_right (bound W labels capacities) 1

/-- The literal postprocessor's physical run pays its final halt and retains
its output choice in the same extended heap used by the construction. -/
theorem choice_bit {n H A : ℕ} (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (capacity : Row n) (hn : 0<n) (initial : BitState 484) (bounded : initial.Bounded H A)
    (pc0 : initial.pc=480) (dense : value initial.next=initial.heap.length) (empty : initial.stack=[])
    {q : Option (BinaryFractionalGraphOracle.Selected n)}
    (selected : DemandCollection.SelectedOrigin (eraseState initial).heap (eraseState initial).registers.a label q)
    (context : CapacityBottleneck.GraphContext (eraseState initial).heap (eraseState initial).registers.b label capacity)
    (W : ℕ) (labels : ∀ i,(label i).length≤W)
    (capacities : ∀ i,(get capacity i).num.length≤W ∧ (get capacity i).den.length≤W) :
    ∃ steps charge out,Run program steps charge initial [] out ∧
      StoredChoice (eraseState out).heap (eraseState out).registers.d label (choice capacity hn q) ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=481 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations≤completeBound 484 H A (instructionBound q W+1) := by
  have dense' : (eraseState initial).next=(eraseState initial).heap.length := by
    simpa [eraseState,State.map] using dense
  have empty' : (eraseState initial).stack=[] := by simp [eraseState,State.map,empty]
  obtain ⟨steps,ext,root,high,stored,bound⟩ := choice_high label hlabel capacity hn
    (eraseState initial) pc0 dense' empty' selected context
  obtain ⟨charge,out,run,erase,_,_,src⟩ := polynomial_simulation bounded high
  have stop : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase] at obs
    have halt : tickNatural program
        (state ((eraseState initial).heap++ext) ((eraseState initial).next+ext.length)
          (eraseState initial).registers.a (eraseState initial).registers.b
          (eraseState initial).registers.c root [] (eraseState initial).source 481)=none := by
      simp [tickNatural,program,state]
    rw [halt] at obs
    cases htick : tick program out with
    | none => rfl
    | some x => simp [htick] at obs
  refine ⟨steps,charge,out,run,?_,by simpa [state,eraseState,State.map] using src,?_,?_,⟨ext,?_⟩,stop,?_⟩
  · rw [erase];exact stored
  · have h : (eraseState out).stack=[] := by rw [erase];rfl
    simpa [eraseState,State.map] using h
  · have h : (eraseState out).pc=481 := by rw [erase];rfl
    exact h
  · rw [erase];rfl
  · exact (terminal_accounting run bounded stop).2.trans
      (SupportSearchEncoding.complete_mono 484 H A _ _ (bound W labels capacities))

end DirectedFlowCutGap.OracleChoice
