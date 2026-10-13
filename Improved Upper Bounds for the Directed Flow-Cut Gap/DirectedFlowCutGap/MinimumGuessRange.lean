import DirectedFlowCutGap.ActualMinimumGuess
import DirectedFlowCutGap.SourcePackingBoundMonotonicity

namespace DirectedFlowCutGap.MinimumGuess
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead

def gridShiftedWidth (rows : List Fraction) : ℕ :=
  LambdaRowProgram.rowBits rows+(3*LambdaRowProgram.rowBits rows+3*rows.length+7)+2

def gridInputSteps (d : ℕ) (rows : List Fraction) (exponent : Bits) : ℕ :=
  MinimumShift.gridInputSteps rows exponent+
    EnumeratedPacking.instructionBound d rows.length (gridShiftedWidth rows)+12

theorem inputSteps_le_grid (d : ℕ) (rows : List Fraction) (exponent : Bits)
    (range : value exponent ≤ LambdaGridProgram.gridLimit rows) :
    inputSteps d rows exponent ≤ gridInputSteps d rows exponent := by
  have prep := MinimumShift.inputSteps_le_grid rows exponent range
  have lim := LambdaGridProgram.gridLimit_bound rows
  have sw : shiftedWidth rows exponent ≤ gridShiftedWidth rows := by
    unfold shiftedWidth gridShiftedWidth ShiftedGridProgram.scalarWidth
    omega
  have solver := SourcePackingBound.mono_EnumeratedPacking_instructionBound
    (Nat.le_refl d) (Nat.le_refl rows.length) sw
  unfold inputSteps gridInputSteps
  omega

/-- The later original grid loop must derive its finite-range invariant. -/
theorem guess_grid_bit {n H B : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n) (exponent : Bits)
    {xs : List DemandCollection.Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (DemandCollection.EncodesDemand RowVertices.vertexLabel) xs ds)
    (initial : BitState 10000) (bounded : initial.Bounded H B) (pc0 : initial.pc=9998)
    (dense : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (table : WordPairTableRead.Table (eraseState initial).heap (eraseState initial).registers.a
      (IndexedRationalRead.fields costs.toList))
    (exp : BoolList (eraseState initial).heap (eraseState initial).registers.b exponent)
    (graph : GraphAdjacencyProgram.Matrix (eraseState initial).heap (eraseState initial).registers.c
      (GraphRelaxationRefinement.matrix adjacency))
    (pairs : DemandCollection.DemandList (eraseState initial).heap (eraseState initial).registers.d xs)
    (range : value exponent ≤ LambdaGridProgram.gridLimit costs.toList) :
    ∃ k charge out,Run program k charge initial [] out ∧
      Result (eraseState out).heap (eraseState out).registers.d (result adjacency ds costs exponent) ∧
      out.source=initial.source ∧ (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 10000 H B
        (gridInputSteps ds.length costs.toList exponent) := by
  obtain ⟨k,charge,out,run,rep,_,_,_,_,source,_,_,_,_,stop,paid⟩ :=
    guess_bit adjacency costs exponent encoded initial bounded pc0 dense empty table exp graph pairs
  have h:=inputSteps_le_grid ds.length costs.toList exponent range
  exact ⟨k,charge,out,run,rep,source,stop,paid.trans (SupportSearchEncoding.complete_mono 10000 H B _ _ h)⟩
end DirectedFlowCutGap.MinimumGuess
