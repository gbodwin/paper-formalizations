import DirectedFlowCutGap.NormalizedRowBounds

namespace DirectedFlowCutGap.NormalizedRow
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

/-- Actual mask, sum and division run on one heap. No scalar length or normalized
row is supplied; the lower run constructs both and includes its final halt. -/
theorem normalized_bit {xs : List Fraction} {mask : List Bool} {H A : ℕ}
    (initial : BitState 372) (bounded : initial.Bounded H A) (pc0 : initial.pc=364)
    (hn : value initial.next=initial.heap.length)
    (row : StoredList (eraseState initial).heap (eraseState initial).registers.a xs)
    (flags : BoolList (eraseState initial).heap (eraseState initial).registers.b mask)
    (aligned : xs.length=mask.length) (empty : initial.stack=[]) (B : ℕ)
    (rowWidth : ∀ x∈xs,StoredBounded x B) :
    ∃ charge out maskedRoot,Run program (steps xs mask) charge initial [] out ∧
      StoredList (eraseState out).heap (eraseState out).registers.d (result xs mask) ∧
      Stored (eraseState out).heap (eraseState out).registers.b (alpha xs mask) ∧
      StoredList (eraseState out).heap maskedRoot (MaskedRationalRow.result xs mask) ∧
      StoredList (eraseState out).heap (eraseState initial).registers.a xs ∧
      BoolList (eraseState out).heap (eraseState initial).registers.b mask ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=371 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext ∧ ext.length=cells xs mask) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 372 H A (instructionBound xs.length B) := by
  have hn' : (eraseState initial).next=(eraseState initial).heap.length := by
    simpa [eraseState,State.map] using hn
  have hs : (eraseState initial).stack=[] := by simp [eraseState,State.map,empty]
  obtain ⟨ext,rm,rs,root,len,high,rep,scalar,masked⟩ := normalized_high (eraseState initial) pc0 hn' row flags aligned hs
  obtain ⟨charge,out,run,erase,_,_,source⟩ := polynomial_simulation bounded high
  have halt : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase] at obs
    have hn : tickNatural program
        (state ((eraseState initial).heap++ext) ((eraseState initial).next+ext.length)
          (eraseState initial).registers.a rs (eraseState initial).next root [] (eraseState initial).source 371)=none := rfl
    rw [hn] at obs
    cases ht : tick program out with
    | none => rfl
    | some r => simp [ht] at obs
  have cost := (terminal_accounting run bounded halt).2
  have hb := steps_bound xs mask B aligned rowWidth
  have hm : completeBound 372 H A (steps xs mask) ≤ completeBound 372 H A (instructionBound xs.length B) := by
    unfold completeBound runBound stepBound
    gcongr
  refine ⟨charge,out,rm,run,?_,?_,?_,?_,?_,source,?_,?_,⟨ext,?_,len⟩,halt,cost.trans hm⟩
  · rw [erase];exact rep
  · rw [erase];exact scalar
  · rw [erase];exact masked
  · rw [erase];exact list_extend row ext
  · rw [erase];exact boolList_extend flags ext
  · have h : (eraseState out).stack=[] := by rw [erase];rfl
    simpa [eraseState,State.map] using h
  · have h : (eraseState out).pc=371 := by rw [erase];rfl
    exact h
  · rw [erase];rfl
end DirectedFlowCutGap.NormalizedRow
