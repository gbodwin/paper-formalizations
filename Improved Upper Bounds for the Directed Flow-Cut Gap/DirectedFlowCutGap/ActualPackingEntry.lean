import DirectedFlowCutGap.PackingEntryBounds

namespace DirectedFlowCutGap.PackingEntry
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram

theorem result_eq_update {n : ℕ} (capacity y : Row n) (mask : Vector Bool n) (i j : Fin n)
    (selected : mask[i.val]=true) :
    get (BinaryFractionalRows.update capacity y mask j).1 i=
      result (get capacity i) (get capacity j) (get y i) := by
  simp [BinaryFractionalRows.update,EncodedRoundingInput.tabulate_value,BinaryFractionalRows.get,selected,
    BinaryFractionalRows.factor,result,factor,quotient,doubled]

/-- The selected entry update executes four arithmetic calls and constructs
both small constants. Supplied original widths bound all intermediate fields;
no factor, quotient or updated value is an input. -/
theorem entry_bit (ci amount y : Fraction) {H A : ℕ} (initial : BitState 480)
    (bounded : initial.Bounded H A) (pc0 : initial.pc=440)
    (dense : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (cap : Stored (eraseState initial).heap (eraseState initial).registers.a ci)
    (amt : Stored (eraseState initial).heap (eraseState initial).registers.b amount)
    (weight : Stored (eraseState initial).heap (eraseState initial).registers.c y)
    (B : ℕ) (hc : StoredBounded ci B) (ha : StoredBounded amount B) (hy : StoredBounded y B) :
    ∃ charge out,Run program (steps ci amount y) charge initial [] out ∧
      Stored (eraseState out).heap (eraseState out).registers.d (result ci amount y) ∧
      Stored (eraseState out).heap (eraseState initial).registers.a ci ∧
      Stored (eraseState out).heap (eraseState initial).registers.b amount ∧
      Stored (eraseState out).heap (eraseState initial).registers.c y ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=467 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext ∧ ext.length=cells ci amount y) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 480 H A (instructionBound B) := by
  have dense' : (eraseState initial).next=(eraseState initial).heap.length := by
    simpa [eraseState,State.map] using dense
  have start : state (eraseState initial).heap (eraseState initial).next
      (eraseState initial).registers.a (eraseState initial).registers.b
      (eraseState initial).registers.c (eraseState initial).registers.d [] initial.source 440=
      eraseState initial := by
    cases initial
    simp_all [eraseState,State.map,state]
  obtain ⟨ext,factorRoot,root,len,high,rep⟩ := entry_high ci amount y cap amt weight
    (eraseState initial).next (eraseState initial).registers.d dense' initial.source
  rw [start] at high
  obtain ⟨charge,out,run,erase,_,_,source⟩ := polynomial_simulation bounded high
  have halt : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase] at obs
    have hh : tickNatural program
        (state ((eraseState initial).heap++ext) ((eraseState initial).next+ext.length)
          (eraseState initial).registers.c factorRoot ((eraseState initial).next+9) root [] initial.source 467)=none := rfl
    rw [hh] at obs
    cases ht : tick program out with
    | none => rfl
    | some r => simp [ht] at obs
  have cost := (terminal_accounting run bounded halt).2
  have hb := steps_bound ci amount y B hc ha hy
  have hm : completeBound 480 H A (steps ci amount y) ≤ completeBound 480 H A (instructionBound B) := by
    unfold completeBound runBound stepBound
    gcongr
  refine ⟨charge,out,run,?_,?_,?_,?_,source,?_,?_,⟨ext,?_,len⟩,halt,cost.trans hm⟩
  · rw [erase];exact rep
  · rw [erase];exact stored_extend cap ext
  · rw [erase];exact stored_extend amt ext
  · rw [erase];exact stored_extend weight ext
  · have hs : (eraseState out).stack=[] := by rw [erase];rfl
    simpa [eraseState,State.map] using hs
  · have hp : (eraseState out).pc=467 := by rw [erase];rfl
    exact hp
  · rw [erase];rfl
end DirectedFlowCutGap.PackingEntry
