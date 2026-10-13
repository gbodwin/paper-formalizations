import DirectedFlowCutGap.ActualMinimumShift

namespace DirectedFlowCutGap.MinimumShift
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead

def gridInputSteps (rows : List Fraction) (exponent : Bits) : ℕ :=
  OriginalRowMinimum.inputSteps rows+
    ShiftedGridProgram.gridInputSteps rows (List.replicate rows.length false) exponent+8

theorem inputSteps_le_grid (rows : List Fraction) (exponent : Bits)
    (range : value exponent ≤ LambdaGridProgram.gridLimit rows) :
    inputSteps rows exponent ≤ gridInputSteps rows exponent := by
  have h:=ShiftedGridProgram.inputSteps_le_grid rows (List.replicate rows.length false) exponent range
  unfold inputSteps gridInputSteps;omega

/-- The later grid controller must establish its original finite-range invariant. -/
theorem shifted_grid_bit {H A n : ℕ} (costs : BinaryFractionalRows.Row n) {exponent : Bits}
    (initial : BitState 1560) (bounded : initial.Bounded H A) (pc0 : initial.pc=1558)
    (dense : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (table : WordPairTableRead.Table (eraseState initial).heap (eraseState initial).registers.a
      (IndexedRationalRead.fields costs.toList))
    (exp : BoolList (eraseState initial).heap (eraseState initial).registers.c exponent)
    (range : value exponent ≤ LambdaGridProgram.gridLimit costs.toList) :
    ∃ k charge out,k ≤ gridInputSteps costs.toList exponent ∧ Run program k charge initial [] out ∧
      Result (eraseState out).heap (eraseState out).registers.d (result costs exponent) ∧
      out.source=initial.source ∧ (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 1560 H A (gridInputSteps costs.toList exponent) := by
  obtain ⟨k,charge,out,hk,run,rep,_,_,source,_,_,_,stop,paid⟩ :=
    shifted_bit costs initial bounded pc0 dense empty table exp
  have h:=inputSteps_le_grid costs.toList exponent range
  exact ⟨k,charge,out,hk.trans h,run,rep,source,stop,paid.trans
    (SupportSearchEncoding.complete_mono 1560 H A _ _ h)⟩
theorem result_original {n : ℕ} (costs : BinaryFractionalRows.Row n) (exponent : Bits) :
    result costs exponent=(BinaryFractionalDispatch.minimumPositive costs).1.map (fun i =>
      (BinaryFractionalGuesses.shifted costs
        (BinaryFractionalGuesses.lambda costs i (BinaryFractionalCore.dimension costs).1 exponent).1).1.toList) := by
  cases hm : (BinaryFractionalDispatch.minimumPositive costs).1 with
  | none => simp [result,hm]
  | some i =>
    simpa [result,hm] using congrArg some
      (ShiftedGridProgram.result_original costs i (RowVertices.vertexLabel i) exponent (RowVertices.label_numeric i))
end DirectedFlowCutGap.MinimumShift
