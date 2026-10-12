import DirectedFlowCutGap.GraphRoundBounds

/-! Same lower-machine execution for actual bounded graph discovery, including
its terminal halt. The polynomial instruction bound uses only represented input
sizes, index caps and canonical field widths. -/
namespace DirectedFlowCutGap.GraphDiscoveryProgram
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open GraphWalkExtension

theorem minimize_high {vertices adjacency : List Bits} {rows : List Fraction} {sw target u : Bits}
    (initial : NaturalState 720) (pc0 : initial.pc=717)
    (hn : initial.next=initial.heap.length) (empty : initial.stack=[])
    (input : Vertices initial.heap initial.registers.a vertices)
    (context : GlobalContext initial.heap initial.registers.b vertices adjacency rows sw target)
    (word : BoolList initial.heap initial.registers.c u)
    (hi : ∀ v∈vertices,value v<adjacency.length) (hc : ∀ v∈vertices,value v<rows.length)
    (targetCol : ∀ v,(hv : v∈vertices) → value target<(adjacency[value v]'(hi v hv)).length)
    (columns : ∀ v,(hv : v∈vertices) → ∀ z∈vertices,value z<(adjacency[value v]'(hi v hv)).length) :
    ∃ ext root,ext.length=minimizeCells vertices adjacency rows sw target u ∧
      NaturalRun program (minimizeSteps vertices adjacency rows sw target u+1) initial []
        (state (initial.heap++ext) (initial.next+ext.length) initial.registers.a initial.registers.b
          initial.registers.c root [] initial.source 719) ∧
      StoredOption (initial.heap++ext) root (minimize vertices adjacency rows sw target u) := by
  cases initial with
  | mk heap next regs stack pc source =>
    cases regs with
    | mk a b c d =>
      simp only at pc0 hn empty input context word
      subst pc;subst stack
      obtain ⟨ext,root,len,body,rep⟩ := minimize_return input context word hi hc targetCol columns
        next d hn ⟨a,b,c,d⟩ 719 [] source
      have first : tickNatural program (state heap next a b c d [] source 717)=
          some ⟨state heap next a b c d [⟨719,.r3,⟨a,b,c,d⟩⟩] source 700,[],0⟩ := by
        simp [tickNatural,program,state]
      exact ⟨ext,root,len,by simpa [state] using NaturalRun.step first body,rep⟩

theorem minimize_bit {vertices adjacency : List Bits} {rows : List Fraction} {sw target u : Bits}
    {H A : ℕ} (initial : BitState 720) (bounded : initial.Bounded H A) (pc0 : initial.pc=717)
    (hn : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (input : Vertices (eraseState initial).heap (eraseState initial).registers.a vertices)
    (context : GlobalContext (eraseState initial).heap (eraseState initial).registers.b vertices adjacency rows sw target)
    (word : BoolList (eraseState initial).heap (eraseState initial).registers.c u)
    (hi : ∀ v∈vertices,value v<adjacency.length) (hc : ∀ v∈vertices,value v<rows.length)
    (targetCol : ∀ v,(hv : v∈vertices) → value target<(adjacency[value v]'(hi v hv)).length)
    (columns : ∀ v,(hv : v∈vertices) → ∀ z∈vertices,value z<(adjacency[value v]'(hi v hv)).length)
    (B N : ℕ) (hB : 1 ≤ B) (hr : ∀ q∈rows,StoredBounded q B)
    (ht : target.length ≤ B) (it : value target ≤ N) (hu : u.length ≤ B)
    (hv : ∀ v∈vertices,v.length ≤ B ∧ value v ≤ N) :
    ∃ charge out,Run program (minimizeSteps vertices adjacency rows sw target u+1) charge initial [] out ∧
      StoredOption (eraseState out).heap (eraseState out).registers.d (minimize vertices adjacency rows sw target u) ∧
      Vertices (eraseState out).heap (eraseState initial).registers.a vertices ∧
      GlobalContext (eraseState out).heap (eraseState initial).registers.b vertices adjacency rows sw target ∧
      BoolList (eraseState out).heap (eraseState initial).registers.c u ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=719 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext ∧
        ext.length=minimizeCells vertices adjacency rows sw target u) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 720 H A (discoveryBudget vertices.length B N sw.length) := by
  have hn' : (eraseState initial).next=(eraseState initial).heap.length := by simpa [eraseState,State.map] using hn
  have empty' : (eraseState initial).stack=[] := by simp [eraseState,State.map,empty]
  obtain ⟨ext,root,len,high,rep⟩ := minimize_high (eraseState initial) pc0 hn' empty' input context word hi hc targetCol columns
  obtain ⟨charge,out,run,erase,_,_,src⟩ := polynomial_simulation bounded high
  have stop : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase] at obs
    have halt : tickNatural program
        (state ((eraseState initial).heap++ext) ((eraseState initial).next+ext.length)
          (eraseState initial).registers.a (eraseState initial).registers.b
          (eraseState initial).registers.c root [] (eraseState initial).source 719)=none := by
      simp [tickNatural,program,state]
    rw [halt] at obs
    cases ht : tick program out with
    | none => rfl
    | some x => simp [ht] at obs
  have cost := (terminal_accounting run bounded stop).2
  have hs := minimize_bound vertices adjacency rows sw target u B N hB hr ht it hu hc hv
  have hm : completeBound 720 H A (minimizeSteps vertices adjacency rows sw target u+1) ≤
      completeBound 720 H A (discoveryBudget vertices.length B N sw.length) := by
    unfold completeBound runBound stepBound
    gcongr
  refine ⟨charge,out,run,?_,?_,?_,?_,by simpa [state,eraseState,State.map] using src,
    ?_,?_,⟨ext,?_,len⟩,stop,cost.trans hm⟩
  · rw [erase];exact rep
  · rw [erase];exact vertices_extend input ext
  · rw [erase];exact global_extend context ext
  · rw [erase];exact PackedBooleanConstructor.boolList_extend word ext
  · have h : (eraseState out).stack=[] := by rw [erase];rfl
    simpa [eraseState,State.map] using h
  · have h : (eraseState out).pc=719 := by rw [erase];rfl
    exact h
  · rw [erase];rfl

end DirectedFlowCutGap.GraphDiscoveryProgram
