import DirectedFlowCutGap.PackingUpdateRowRefinement

namespace DirectedFlowCutGap.PackingUpdateRow
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

/-- The actual mask controls each arithmetic call; the ordered output spine and
all updated records are produced by this same paid physical run. -/
theorem row_bit (amount : Fraction) {cs ys : List Fraction} {mask : List Bool} {H A : ℕ}
    (initial : BitState 520) (bounded : initial.Bounded H A) (pc0 : initial.pc=518)
    (hn : value initial.next=initial.heap.length)
    (cap : StoredList (eraseState initial).heap (eraseState initial).registers.a cs)
    (weights : StoredList (eraseState initial).heap (eraseState initial).registers.b ys)
    {mr ar : ℕ} (flags : BoolList (eraseState initial).heap mr mask)
    (amt : Stored (eraseState initial).heap ar amount)
    (context : (eraseState initial).heap[(eraseState initial).registers.c]?=some (.pair mr ar))
    (aligned : cs.length=ys.length) (alignedMask : cs.length=mask.length)
    (empty : initial.stack=[]) (B : ℕ) (amountWidth : StoredBounded amount B)
    (capWidth : ∀ x∈cs,StoredBounded x B) (rowWidth : ∀ x∈ys,StoredBounded x B) :
    ∃ charge out,Run program (1+steps amount cs ys mask) charge initial [] out ∧
      StoredList (eraseState out).heap (eraseState out).registers.a (result amount cs ys mask) ∧
      StoredList (eraseState out).heap (eraseState initial).registers.a cs ∧
      StoredList (eraseState out).heap (eraseState initial).registers.b ys ∧
      BoolList (eraseState out).heap mr mask ∧ Stored (eraseState out).heap ar amount ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=519 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext ∧ ext.length=cells amount cs ys mask) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 520 H A (instructionBound cs.length B) := by
  have hn' : (eraseState initial).next=(eraseState initial).heap.length := by
    simpa [eraseState,State.map] using hn
  have hs : (eraseState initial).stack=[] := by simp [eraseState,State.map,empty]
  obtain ⟨ext,root,len,high,rep⟩ := row_high amount (eraseState initial) pc0 hn' cap weights flags amt
    context aligned alignedMask hs
  obtain ⟨charge,out,run,erase,_,_,source⟩ := polynomial_simulation bounded high
  have halt : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase] at obs
    have hn : tickNatural program
        (state ((eraseState initial).heap++ext) ((eraseState initial).next+ext.length)
          root (eraseState initial).registers.b (eraseState initial).registers.c
          (eraseState initial).registers.d [] (eraseState initial).source 519)=none := rfl
    rw [hn] at obs
    cases ht : tick program out with
    | none => rfl
    | some r => simp [ht] at obs
  have cost := (terminal_accounting run bounded halt).2
  have hb := steps_bound amount cs ys mask B amountWidth capWidth rowWidth
  have hm : completeBound 520 H A (1+steps amount cs ys mask) ≤
      completeBound 520 H A (instructionBound cs.length B) := by
    unfold completeBound runBound stepBound
    gcongr
  refine ⟨charge,out,run,?_,?_,?_,?_,?_,source,?_,?_,⟨ext,?_,len⟩,halt,cost.trans hm⟩
  · rw [erase];exact rep
  · rw [erase];exact list_extend cap ext
  · rw [erase];exact list_extend weights ext
  · rw [erase];exact boolList_extend flags ext
  · rw [erase];exact stored_extend amt ext
  · have h : (eraseState out).stack=[] := by rw [erase];rfl
    simpa [eraseState,State.map] using h
  · have h : (eraseState out).pc=519 := by rw [erase];rfl
    exact h
  · rw [erase];rfl
end DirectedFlowCutGap.PackingUpdateRow
