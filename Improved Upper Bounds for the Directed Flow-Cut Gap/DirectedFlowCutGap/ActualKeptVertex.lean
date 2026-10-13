import DirectedFlowCutGap.KeptVertexExecution

namespace DirectedFlowCutGap.KeptVertex
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor

theorem keep {heap : NaturalHeap} {word context : ℕ} {s t u : Bits} {zero : Bool}
    (hu : BoolList heap word u) (hc : Context heap context s t zero)
    (next c d : ℕ) (hn : next=heap.length) (stack : List (Frame ℕ 80)) (source : Bits) :
    ∃ ext root,ext.length=keepCells s t u zero ∧ NaturalRun program (keepSteps s t u zero+1)
      (state heap next word context c d stack source 78) []
      (state (heap++ext) (next+ext.length) word context c root stack source 79) ∧
      (heap++ext)[root]?=some (.flag (bit s t u zero)) := by
  obtain ⟨ext,root,len,run,rep⟩ := keep_return hu hc next c d hn ⟨word,context,c,d⟩ 79 stack source
  have call : tickNatural program (state heap next word context c d stack source 78)=
      some ⟨state heap next word context c d (⟨79,.r3,⟨word,context,c,d⟩⟩::stack) source 50,[],0⟩ := by rfl
  exact ⟨ext,root,len,by simpa [Nat.add_comm] using NaturalRun.step call run,rep⟩

theorem keep_bit {H A : ℕ} {s t u : Bits} {zero : Bool}
    (initial : BitState 80) (bounded : initial.Bounded H A) (pc0 : initial.pc=78)
    (dense : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (hu : BoolList (eraseState initial).heap (eraseState initial).registers.a u)
    (hc : Context (eraseState initial).heap (eraseState initial).registers.b s t zero) :
    ∃ charge out, Run program (keepSteps s t u zero+1) charge initial [] out ∧
      (eraseState out).heap[(eraseState out).registers.d]?=some (.flag (bit s t u zero)) ∧
      BoolList (eraseState out).heap (eraseState initial).registers.a u ∧
      Context (eraseState out).heap (eraseState initial).registers.b s t zero ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=79 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext ∧ ext.length=keepCells s t u zero) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 80 H A
        (32*(s.length+t.length+u.length+2)+1) := by
  have dense' : (eraseState initial).next=(eraseState initial).heap.length := by
    simpa [eraseState,State.map] using dense
  have start : state (eraseState initial).heap (eraseState initial).next
      (eraseState initial).registers.a (eraseState initial).registers.b (eraseState initial).registers.c
      (eraseState initial).registers.d (eraseState initial).stack initial.source 78=eraseState initial := by
    cases initial
    simp_all [eraseState,State.map,state]
  obtain ⟨ext,root,len,high,rep⟩ := keep hu hc (eraseState initial).next
    (eraseState initial).registers.c (eraseState initial).registers.d dense'
    (eraseState initial).stack initial.source
  rw [start] at high
  have halt : tickNatural program (state ((eraseState initial).heap++ext)
      ((eraseState initial).next+ext.length) (eraseState initial).registers.a
      (eraseState initial).registers.b (eraseState initial).registers.c root
      (eraseState initial).stack initial.source 79)=none := by simp [tickNatural,state,program]
  obtain ⟨charge,out,run,erase,_,_,sourceOut⟩ := polynomial_simulation bounded high
  have stop : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase,halt] at obs
    cases h : tick program out with
    | none => rfl
    | some r => simp [h] at obs
  refine ⟨charge,out,run,?_,?_,?_,sourceOut,?_,?_,⟨ext,?_,len⟩,stop,
    (terminal_accounting run bounded stop).2.trans
      (SupportSearchEncoding.complete_mono 80 H A _ _ (keep_steps_bound s t u zero))⟩
  · simpa only [erase,state] using rep
  · rw [erase];exact boolList_extend hu ext
  · rw [erase];exact context_extend hc ext
  · have h : (eraseState out).stack=(eraseState initial).stack := by rw [erase];rfl
    simpa [eraseState,State.map,empty] using h
  · have h : (eraseState out).pc=79 := by rw [erase];rfl
    exact h
  · rw [erase];rfl

theorem bit_encode {n : ℕ} (label : Fin n → Bits) (hlabel : ∀ i,value (label i)=i.val)
    (s t u : Fin n) (zero : Bool) :
    bit (label s) (label t) (label u) zero=(!zero || decide (u=s) || decide (u=t)) := by
  simp only [bit,same,SupportSearchEncoding.same_label label hlabel]
end DirectedFlowCutGap.KeptVertex
