import DirectedFlowCutGap.ActualShiftedGrid

namespace DirectedFlowCutGap.ShiftedGridProgram
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal
open BooleanTableRead RationalComparisonProgram CanonicalRationalSum

/-- The later original grid controller must establish this explicit invariant. -/
theorem shifted_grid_bit {H A : ℕ} {rows : List Fraction} {index exponent : Bits}
    (initial : BitState 1220) (bounded : initial.Bounded H A) (pc0 : initial.pc=1218)
    (dense : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (table : WordPairTableRead.Table (eraseState initial).heap (eraseState initial).registers.a (IndexedRationalRead.fields rows))
    (idx : BoolList (eraseState initial).heap (eraseState initial).registers.b index)
    (exp : BoolList (eraseState initial).heap (eraseState initial).registers.c exponent)
    (valid : value index<rows.length) (range : value exponent ≤ LambdaGridProgram.gridLimit rows) :
    ∃ charge out,Run program (steps rows index exponent+1) charge initial [] out ∧
      StoredList (eraseState out).heap (eraseState out).registers.d (result rows index exponent) ∧
      WordPairTableRead.Table (eraseState out).heap (eraseState out).registers.d
        (IndexedRationalRead.fields (result rows index exponent)) ∧
      out.source=initial.source ∧ (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 1220 H A (gridInputSteps rows index exponent) := by
  obtain ⟨charge,out,run,rep,_,_,_,source,_,_,_,stop,paid⟩ :=
    shifted_bit initial bounded pc0 dense empty table idx exp valid
  exact ⟨charge,out,run,rep,ScalarAdditionRow.table_of_stored rep,source,stop,paid.trans
    (SupportSearchEncoding.complete_mono 1220 H A _ _ (inputSteps_le_grid rows index exponent range))⟩
end DirectedFlowCutGap.ShiftedGridProgram
