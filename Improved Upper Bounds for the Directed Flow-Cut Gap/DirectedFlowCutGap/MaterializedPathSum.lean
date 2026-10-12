import DirectedFlowCutGap.PathCostMaterialization

/-! One literal program first materializes outgoing path costs from index words,
then accumulates those same newly constructed records by canonical arithmetic. -/
namespace DirectedFlowCutGap.MaterializedPathSum
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor RationalComparisonProgram

def matLabel (pc : Fin 124) : Fin 284 := ⟨pc.val,by omega⟩
def sumLabel (pc : Fin 158) : Fin 284 := ⟨pc.val+124,by omega⟩
def program : Program 284 := fun pc =>
  if pc.val=123 then .move .r0 .r3 280
  else if pc.val=281 then .ret .r3
  else if h : pc.val<124 then
    ReferenceProgramLabels.instruction matLabel (PathCostMaterialization.program ⟨pc.val,h⟩)
  else if h : pc.val<282 then
    ReferenceProgramLabels.instruction sumLabel (CanonicalRationalSum.program ⟨pc.val-124,by omega⟩)
  else if pc.val=282 then .call 122 283 .r3 else .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 284)) (source : Bits) (pc : Fin 284) : NaturalState 284 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

def steps (rows : List Fraction) (sw : Bits) (words : List Bits) : ℕ :=
  PathCostMaterialization.steps sw words+
    CanonicalRationalSum.steps (PathCostMaterialization.costs rows sw words)+4

def cells (rows : List Fraction) (sw : Bits) (words : List Bits) : ℕ :=
  PathCostMaterialization.cells sw words+
    CanonicalRationalSum.cells (PathCostMaterialization.costs rows sw words)

def result (rows : List Fraction) (sw : Bits) (words : List Bits) : Fraction :=
  (BinaryFractionalRows.sum (PathCostMaterialization.costs rows sw words)).1

theorem mat_slots (pc : Fin 124) (h : PathCostMaterialization.program pc≠.halt) :
    program (matLabel pc)=ReferenceProgramLabels.instruction matLabel (PathCostMaterialization.program pc) := by
  by_cases hp : pc.val=123
  · have he : pc=123 := Fin.ext hp
    subst pc;simp [PathCostMaterialization.program] at h
  · simp [program,matLabel,pc.isLt,hp,show ¬pc.val=281 by omega]

theorem sum_slots (pc : Fin 158) (h : CanonicalRationalSum.program pc≠.halt) :
    program (sumLabel pc)=ReferenceProgramLabels.instruction sumLabel (CanonicalRationalSum.program pc) := by
  by_cases hp : pc.val=157
  · have he : pc=157 := Fin.ext hp
    subst pc;simp [CanonicalRationalSum.program] at h
  · simp [program,sumLabel,show ¬pc.val+124=123 by omega,show ¬pc.val+124=281 by omega,
      show ¬pc.val+124<124 by omega,show pc.val+124<282 by omega]

theorem run_append {s u v : NaturalState 284} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

/-- The retained path indices are traversed and their real outgoing row values
are summed. The returned cost is constructed by this execution. -/
theorem sum_return {words : List Bits} {sw : Bits} {rows : List Fraction} {heap : NaturalHeap} {a b : ℕ}
    (input : PathCostMaterialization.WordList heap a words)
    (context : OutgoingCostProgram.Context heap b rows sw) (valid : ∀ w∈words,value w<rows.length)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 284)
    (stack : List (Frame ℕ 284)) (source : Bits) :
    ∃ ext root,ext.length=cells rows sw words ∧ NaturalRun program (steps rows sw words)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 122) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      Stored (heap++ext) root (result rows sw words) ∧
      ∃ costRoot,CanonicalRationalSum.StoredList (heap++ext) costRoot (PathCostMaterialization.costs rows sw words) := by
  let frames := (⟨pc,.r3,saved⟩::stack)
  obtain ⟨em,rm,lm,matRun,matRep⟩ := PathCostMaterialization.materialize_high
    (PathCostMaterialization.state heap next a b c d [] source 122) rfl hn rfl input context valid
  let h1 := heap++em
  let n1 := next+em.length
  have dense1 : n1=h1.length := by simp [n1,h1,hn]
  obtain ⟨es,rs,ls,sumRun,sumRep⟩ := CanonicalRationalSum.sum_high
    (CanonicalRationalSum.state h1 n1 rm b c rm [] source 156) rfl dense1 matRep rfl
  have mlift := ReferenceProgramLabels.run matLabel PathCostMaterialization.program program mat_slots matRun
  have mlift := ReferenceProgramStack.run program frames mlift
  have mbody : NaturalRun program (PathCostMaterialization.steps sw words+1)
      (state heap next a b c d frames source 122) []
      (state h1 n1 a b c rm frames source 123) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,ReferenceProgramStack.state,
      PathCostMaterialization.state,matLabel,state] using mlift
  have slift := ReferenceProgramLabels.run sumLabel CanonicalRationalSum.program program sum_slots sumRun
  have slift := ReferenceProgramStack.run program frames slift
  have sbody : NaturalRun program (1+CanonicalRationalSum.steps (PathCostMaterialization.costs rows sw words))
      (state h1 n1 rm b c rm frames source 280) []
      (state (h1++es) (n1+es.length) rm b c rs frames source 281) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,ReferenceProgramStack.state,
      CanonicalRationalSum.state,sumLabel,state] using slift
  have move : tickNatural program (state h1 n1 a b c rm frames source 123)=
      some ⟨state h1 n1 rm b c rm frames source 280,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  have ret : tickNatural program (state (h1++es) (n1+es.length) rm b c rs frames source 281)=
      some ⟨state (h1++es) (n1+es.length) saved.a saved.b saved.c rs stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,frames,Registers.get,Registers.set]
  refine ⟨em++es,rs,by simp [cells,lm,ls],?_,?_,rm,?_⟩
  · have all := run_append mbody (run_append (.step move (.done _)) (run_append sbody (.step ret (.done _))))
    convert all using 1 <;> simp [steps,h1,n1,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]; omega
  · simpa [result,h1,CanonicalRationalSum.state,List.append_assoc] using sumRep
  · simpa [h1,PathCostMaterialization.state,List.append_assoc] using CanonicalRationalSum.list_extend matRep es

theorem sum_high {words : List Bits} {sw : Bits} {rows : List Fraction} (initial : NaturalState 284)
    (pc0 : initial.pc=282) (hn : initial.next=initial.heap.length) (empty : initial.stack=[])
    (input : PathCostMaterialization.WordList initial.heap initial.registers.a words)
    (context : OutgoingCostProgram.Context initial.heap initial.registers.b rows sw)
    (valid : ∀ w∈words,value w<rows.length) :
    ∃ ext root,ext.length=cells rows sw words ∧ NaturalRun program (steps rows sw words+1) initial []
      (state (initial.heap++ext) (initial.next+ext.length) initial.registers.a
        initial.registers.b initial.registers.c root [] initial.source 283) ∧
      Stored (initial.heap++ext) root (result rows sw words) ∧
      ∃ costRoot,CanonicalRationalSum.StoredList (initial.heap++ext) costRoot (PathCostMaterialization.costs rows sw words) := by
  cases initial with
  | mk heap next regs stack pc source =>
    cases regs with
    | mk a b c d =>
      simp only at pc0 hn empty input context
      subst pc;subst stack
      have first : tickNatural program (state heap next a b c d [] source 282)=
          some ⟨state heap next a b c d [⟨283,.r3,⟨a,b,c,d⟩⟩] source 122,[],0⟩ := by
        simp [tickNatural,program,state]
      obtain ⟨ext,root,len,run,rep,costRep⟩ := sum_return input context valid next c d hn ⟨a,b,c,d⟩ 283 [] source
      exact ⟨ext,root,len,by simpa [Nat.add_assoc,state] using NaturalRun.step first run,rep,costRep⟩
def instructionBound (m B N sourceLength : ℕ) : ℕ :=
  m*(100*(sourceLength+B+N+1)+11)+CanonicalRationalSum.instructionBound m B+7

theorem steps_bound (rows : List Fraction) (sw : Bits) (words : List Bits) (B N : ℕ)
    (hB : 1 ≤ B) (rowWidths : ∀ x∈rows,StoredBounded x B)
    (wordWidths : ∀ w∈words,w.length ≤ B)
    (valid : ∀ w∈words,value w<rows.length) (indices : ∀ w∈words,value w ≤ N) :
    steps rows sw words+1 ≤ instructionBound words.length B N sw.length := by
  have hm := PathCostMaterialization.steps_bound sw words B N wordWidths indices
  have hs := CanonicalRationalSum.steps_bound (PathCostMaterialization.costs rows sw words) B
    (PathCostMaterialization.costs_width rows sw words B hB rowWidths valid)
  simp only [PathCostMaterialization.costs,List.length_map] at hs
  dsimp [steps,instructionBound,PathCostMaterialization.costs]
  omega

/-- Complete lower execution, from retained path indices and the row table
through materialization and canonical accumulation, with one final paid halt. -/
theorem sum_bit {words : List Bits} {sw : Bits} {rows : List Fraction} {H A : ℕ} (initial : BitState 284)
    (bounded : initial.Bounded H A) (pc0 : initial.pc=282)
    (hn : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (input : PathCostMaterialization.WordList (eraseState initial).heap (eraseState initial).registers.a words)
    (context : OutgoingCostProgram.Context (eraseState initial).heap (eraseState initial).registers.b rows sw)
    (valid : ∀ w∈words,value w<rows.length) (B N : ℕ) (hB : 1 ≤ B)
    (rowWidths : ∀ x∈rows,StoredBounded x B) (wordWidths : ∀ w∈words,w.length ≤ B)
    (indices : ∀ w∈words,value w ≤ N) :
    ∃ charge out,Run program (steps rows sw words+1) charge initial [] out ∧
      Stored (eraseState out).heap (eraseState out).registers.d (result rows sw words) ∧
      PathCostMaterialization.WordList (eraseState out).heap (eraseState initial).registers.a words ∧
      OutgoingCostProgram.Context (eraseState out).heap (eraseState initial).registers.b rows sw ∧
      (∃ costRoot,CanonicalRationalSum.StoredList (eraseState out).heap costRoot (PathCostMaterialization.costs rows sw words)) ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=283 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext ∧ ext.length=cells rows sw words) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 284 H A (instructionBound words.length B N sw.length) := by
  have hn' : (eraseState initial).next=(eraseState initial).heap.length := by simpa [eraseState,State.map] using hn
  have empty' : (eraseState initial).stack=[] := by simp [eraseState,State.map,empty]
  obtain ⟨ext,root,len,high,rep,costRep⟩ := sum_high (eraseState initial) pc0 hn' empty' input context valid
  obtain ⟨charge,out,run,erase,_,_,src⟩ := polynomial_simulation bounded high
  have stop : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase] at obs
    have halt : tickNatural program
        (state ((eraseState initial).heap++ext) ((eraseState initial).next+ext.length)
          (eraseState initial).registers.a (eraseState initial).registers.b
          (eraseState initial).registers.c root [] (eraseState initial).source 283)=none := by
      simp [tickNatural,program,state]
    rw [halt] at obs
    cases ht : tick program out with
    | none => rfl
    | some x => simp [ht] at obs
  have hc := (terminal_accounting run bounded stop).2
  have hs := steps_bound rows sw words B N hB rowWidths wordWidths valid indices
  have hm : completeBound 284 H A (steps rows sw words+1) ≤
      completeBound 284 H A (instructionBound words.length B N sw.length) := by
    unfold completeBound runBound stepBound
    gcongr
  refine ⟨charge,out,run,?_,?_,?_,?_,by simpa [state,eraseState,State.map] using src,
    ?_,?_,⟨ext,?_,len⟩,stop,hc.trans hm⟩
  · rw [erase];exact rep
  · rw [erase];exact PathCostMaterialization.list_extend input ext
  · rw [erase];exact PathCostMaterialization.context_extend context ext
  · rw [erase];exact costRep
  · have h : (eraseState out).stack=[] := by rw [erase];rfl
    simpa [eraseState,State.map] using h
  · have h : (eraseState out).pc=283 := by rw [erase];rfl
    exact h
  · rw [erase];rfl

end DirectedFlowCutGap.MaterializedPathSum
