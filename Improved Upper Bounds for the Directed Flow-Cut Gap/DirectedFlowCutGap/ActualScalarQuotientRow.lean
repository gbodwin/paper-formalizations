import DirectedFlowCutGap.ScalarQuotientRowBounds

namespace DirectedFlowCutGap.ScalarQuotientRow
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

/-- Each quotient record and list cell is produced by this same physical run.
Both original inputs remain available, and the final terminal attempt is paid. -/
theorem row_bit (mode : Bool) (scalar : Fraction) {xs : List Fraction} {H A : ℕ}
    (initial : BitState 182) (bounded : initial.Bounded H A) (pc0 : initial.pc=180)
    (hn : value initial.next=initial.heap.length)
    (row : StoredList (eraseState initial).heap (eraseState initial).registers.a xs)
    (sc : Stored (eraseState initial).heap (eraseState initial).registers.b scalar)
    (empty : initial.stack=[]) (B : ℕ) (scalarWidth : StoredBounded scalar B)
    (rowWidth : ∀ x∈xs,StoredBounded x B) :
    ∃ charge out,Run (program mode) (1+steps mode scalar xs) charge initial [] out ∧
      StoredList (eraseState out).heap (eraseState out).registers.d (result mode scalar xs) ∧
      StoredList (eraseState out).heap (eraseState initial).registers.a xs ∧
      Stored (eraseState out).heap (eraseState initial).registers.b scalar ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=181 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext ∧ ext.length=cells mode scalar xs) ∧
      (attempt (program mode) out).result=none ∧
      charge+(attempt (program mode) out).operations ≤ completeBound 182 H A (instructionBound xs.length B) := by
  have hn' : (eraseState initial).next=(eraseState initial).heap.length := by
    simpa [eraseState,State.map] using hn
  have hs : (eraseState initial).stack=[] := by simp [eraseState,State.map,empty]
  obtain ⟨ext,root,len,high,rep⟩ := row_high mode scalar (eraseState initial) pc0 hn' row sc hs
  obtain ⟨charge,out,run,erase,_,_,source⟩ := polynomial_simulation bounded high
  have halt : (attempt (program mode) out).result=none := by
    rw [attempt_result]
    have obs := tick_refines (program mode) out
    rw [erase] at obs
    have hn : tickNatural (program mode)
        (state ((eraseState initial).heap++ext) ((eraseState initial).next+ext.length)
          (eraseState initial).registers.a (eraseState initial).registers.b
          (eraseState initial).registers.c root [] (eraseState initial).source 181)=none := rfl
    rw [hn] at obs
    cases ht : tick (program mode) out with
    | none => rfl
    | some r => simp [ht] at obs
  have cost := (terminal_accounting run bounded halt).2
  have hb := steps_bound mode scalar xs B scalarWidth rowWidth
  have hm : completeBound 182 H A (1+steps mode scalar xs) ≤
      completeBound 182 H A (instructionBound xs.length B) := by
    unfold completeBound runBound stepBound
    gcongr
  refine ⟨charge,out,run,?_,?_,?_,source,?_,?_,⟨ext,?_,len⟩,halt,cost.trans hm⟩
  · rw [erase];exact rep
  · rw [erase];exact list_extend row ext
  · rw [erase];exact stored_extend sc ext
  · have h : (eraseState out).stack=[] := by rw [erase];rfl
    simpa [eraseState,State.map] using h
  · have h : (eraseState out).pc=181 := by rw [erase];rfl
    exact h
  · rw [erase];rfl
end DirectedFlowCutGap.ScalarQuotientRow
