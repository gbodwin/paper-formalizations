import DirectedFlowCutGap.PackingZeroMaskExecution

namespace DirectedFlowCutGap.PackingZeroMask
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal
open BooleanTableRead PackedBooleanConstructor

theorem mask_bit {H A : ℕ} {rows : List (Bits × Bits)}
    (initial : BitState 32) (bounded : initial.Bounded H A) (pc0 : initial.pc=30)
    (dense : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (table : WordPairTableRead.Table (eraseState initial).heap (eraseState initial).registers.a rows) :
    ∃ charge out, Run program (steps rows+1) charge initial [] out ∧
      BoolList (eraseState out).heap (eraseState out).registers.d
        (mask rows) ∧
      WordPairTableRead.Table (eraseState out).heap (eraseState initial).registers.a rows ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=31 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext ∧ ext.length=2*rows.length+1) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 32 H A (steps rows+1) := by
  have dense' : (eraseState initial).next=(eraseState initial).heap.length := by
    simpa [eraseState,State.map] using dense
  have start : state (eraseState initial).heap (eraseState initial).next
      (eraseState initial).registers.a (eraseState initial).registers.b (eraseState initial).registers.c
      (eraseState initial).registers.d (eraseState initial).stack initial.source 30=eraseState initial := by
    cases initial
    simp_all [eraseState,State.map,state]
  obtain ⟨ext,root,len,high,rep⟩ := scan table (eraseState initial).next
    (eraseState initial).registers.b (eraseState initial).registers.c (eraseState initial).registers.d
    dense' (eraseState initial).stack initial.source
  rw [start] at high
  have halt : tickNatural program (state ((eraseState initial).heap++ext)
      ((eraseState initial).next+ext.length) (eraseState initial).registers.a
      (eraseState initial).registers.b (eraseState initial).registers.c root
      (eraseState initial).stack initial.source 31)=none := by simp [tickNatural,state,program]
  obtain ⟨charge,out,run,erase,_,_,sourceOut⟩ := polynomial_simulation bounded high
  have stop : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase,halt] at obs
    cases h : tick program out with
    | none => rfl
    | some r => simp [h] at obs
  refine ⟨charge,out,run,?_,?_,sourceOut,?_,?_,⟨ext,?_,len⟩,stop,
    (terminal_accounting run bounded stop).2⟩
  · simpa only [erase,state] using rep
  · rw [erase];exact BinaryIndexedPairRead.table_extend table ext
  · have h : (eraseState out).stack=(eraseState initial).stack := by rw [erase];rfl
    simpa [eraseState,State.map,empty] using h
  · have h : (eraseState out).pc=31 := by rw [erase];rfl
    exact h
  · rw [erase];rfl

end DirectedFlowCutGap.PackingZeroMask
