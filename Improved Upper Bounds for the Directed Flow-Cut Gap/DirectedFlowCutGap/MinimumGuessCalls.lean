import DirectedFlowCutGap.MinimumGuessCallLift
import DirectedFlowCutGap.MinimumGuessWidth

set_option maxRecDepth 32768

namespace DirectedFlowCutGap.MinimumGuess
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead
open CanonicalRationalSum

theorem shift_call {n : ℕ} (costs : BinaryFractionalRows.Row n) {heap : NaturalHeap} {a c : ℕ} {exponent : Bits}
    (table : WordPairTableRead.Table heap a (IndexedRationalRead.fields costs.toList))
    (exp : BoolList heap c exponent) (next b d : ℕ) (dense : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 10000) (stack : List (Frame ℕ 10000)) (source : Bits) :
    ∃ k ext root,k ≤ MinimumShift.inputSteps costs.toList exponent+1 ∧
      NaturalRun program k (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 1558) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      MinimumShift.Result (heap++ext) root (MinimumShift.result costs exponent) := by
  obtain ⟨k,ext,root,bound,run,rep⟩ := MinimumShift.compute costs table exp next b d dense [] source
  have lift := child_return shiftLabel MinimumShift.program shift_slots run rfl rfl
    .r3 .r3 saved pc stack (by rfl)
  exact ⟨k+1,ext,root,by omega,by simpa [MinimumShift.state,shiftLabel,state,Registers.get,Registers.set] using lift,rep⟩

theorem solve_call {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n) (i : Fin n) (exponent : Bits)
    {xs : List DemandCollection.Demand} {ds : List (BinaryFractionalWalkOracle.Pair n)}
    (encoded : List.Forall₂ (DemandCollection.EncodesDemand RowVertices.vertexLabel) xs ds)
    {heap : NaturalHeap} {cap matrix demands : ℕ}
    (caps : StoredList heap cap (shifted costs i exponent).toList)
    (graph : GraphAdjacencyProgram.Matrix heap matrix (GraphRelaxationRefinement.matrix adjacency))
    (pairs : DemandCollection.DemandList heap demands xs)
    (next spare : ℕ) (dense : next=heap.length) (saved : Registers ℕ) (pc : Fin 10000)
    (stack : List (Frame ℕ 10000)) (source : Bits) :
    ∃ k ext root,k ≤ EnumeratedPacking.instructionBound ds.length n (shiftedWidth costs.toList exponent)+1 ∧
      NaturalRun program k (state heap next cap spare matrix demands (⟨pc,.r3,saved⟩::stack) source 9970) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      PackingStart.StateRecord (heap++ext) root RowVertices.vertexLabel
        (BinaryFractionalGuesses.guess adjacency ds costs i (BinaryFractionalCore.dimension costs).1 exponent).state := by
  obtain ⟨k,ext,_vertices,root,run,rep,bound⟩ := EnumeratedPacking.solve_rows adjacency
    (shifted costs i exponent) (Nat.zero_lt_of_lt i.isLt) encoded caps graph pairs next spare dense source
    (shiftedWidth costs.toList exponent) (shifted_width costs i exponent)
  have lift := child_return solveLabel EnumeratedPacking.program solve_slots run rfl rfl
    .r3 .r3 saved pc stack (by rfl)
  exact ⟨k+1,ext,root,by omega,by simpa [EnumeratedPacking.state,solveLabel,state,Registers.get,Registers.set] using lift,rep⟩
end DirectedFlowCutGap.MinimumGuess
