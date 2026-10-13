import DirectedFlowCutGap.OriginalRowMinimumExecution

namespace DirectedFlowCutGap.OriginalRowMinimum
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal
open BooleanTableRead PackedBooleanConstructor

theorem minimum_bit {H A : ℕ} {rows : List BinaryRational.Fraction}
    (initial : BitState 320) (bounded : initial.Bounded H A) (pc0 : initial.pc=318)
    (dense : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (table : WordPairTableRead.Table (eraseState initial).heap (eraseState initial).registers.a (IndexedRationalRead.fields rows)) :
    ∃ k charge out,k ≤ inputSteps rows ∧ Run program k charge initial [] out ∧
      PositiveMinimum.Result (eraseState out).heap (eraseState out).registers.d (result rows) ∧
      WordPairTableRead.Table (eraseState out).heap (eraseState initial).registers.a (IndexedRationalRead.fields rows) ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=319 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 320 H A (inputSteps rows) := by
  have dense' : (eraseState initial).next=(eraseState initial).heap.length := by
    simpa [eraseState,State.map] using dense
  have start : state (eraseState initial).heap (eraseState initial).next
      (eraseState initial).registers.a (eraseState initial).registers.b (eraseState initial).registers.c
      (eraseState initial).registers.d (eraseState initial).stack initial.source 318=eraseState initial := by
    cases initial
    simp_all [eraseState,State.map,state]
  obtain ⟨k,ext,root,hk,high,rep⟩ := compute table (eraseState initial).next
    (eraseState initial).registers.b (eraseState initial).registers.c (eraseState initial).registers.d
    dense' (eraseState initial).stack initial.source
  rw [start] at high
  have halt : tickNatural program (state ((eraseState initial).heap++ext)
      ((eraseState initial).next+ext.length) (eraseState initial).registers.a
      (eraseState initial).registers.b (eraseState initial).registers.c root
      (eraseState initial).stack initial.source 319)=none := by simp [tickNatural,state,program]
  obtain ⟨charge,out,run,erase,_,_,sourceOut⟩ := polynomial_simulation bounded high
  have stop : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase,halt] at obs
    cases h : tick program out with
    | none => rfl
    | some r => simp [h] at obs
  refine ⟨k,charge,out,hk,run,?_,?_,sourceOut,?_,?_,⟨ext,?_⟩,stop,?_⟩
  · simpa only [erase,state] using rep
  · rw [erase];exact BinaryIndexedPairRead.table_extend table ext
  · have h : (eraseState out).stack=(eraseState initial).stack := by rw [erase];rfl
    simpa [eraseState,State.map,empty] using h
  · have h : (eraseState out).pc=319 := by rw [erase];rfl
    exact h
  · rw [erase];rfl
  · exact (terminal_accounting run bounded stop).2.trans
      (SupportSearchEncoding.complete_mono 320 H A _ _ hk)

end DirectedFlowCutGap.OriginalRowMinimum
