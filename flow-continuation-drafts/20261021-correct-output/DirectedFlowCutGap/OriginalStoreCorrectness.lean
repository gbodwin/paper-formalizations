import DirectedFlowCutGap.OriginalStoreDispatch

/-!
UNVERIFIED SOURCE-ONLY DRAFT, 2026-10-21. No elaboration or kernel replay.
Compose the preserved ordinary dispatcher/store drafts with the baseline's
original-input semantic correctness theorem. No existing proof body is changed.
The physical output encodes the ordered state projection, not operation fields.
Preparation remains a declared Boolean/list charge, not a physical parser run.
-/
noncomputable section

namespace DirectedFlowCutGap.OriginalStoreCorrectness
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal
open OriginalStoreInitial

/-- Semantic specification of a high-level output for the actual typed input.
The covers clause includes feasibility and the simultaneous factor-six cost /
factor-twelve mass comparison against every feasible real comparator. -/
def CorrectForInput {n : ℕ} (D : BinaryFractionalGuesses.Input n)
    (output : BinaryFractionalGuesses.Output n) : Prop :=
  FractionalCoverRawGuesses.Correct (BinaryFractionalGuesses.decodeInput D).graph D.demands
    (BinaryFractionalRows.decodeRow D.costs)
    (FractionalCoverRawCore.inputWidth (BinaryFractionalRows.decodeRow D.costs))
    (BinaryFractionalGuesses.decodeOutput output)

/-- This specification cannot certify the invalid tag. -/
theorem correct_not_invalid {n : ℕ} (D : BinaryFractionalGuesses.Input n)
    {output : BinaryFractionalGuesses.Output n} (correct : CorrectForInput D output) :
    output ≠ .invalid := by
  intro invalid
  subst output
  exact correct

/-- Original-input initialization and physical execution return the very output
whose semantics are certified by the baseline theorem. All provenance fields
and the same-run terminal-inclusive bound are retained. -/
theorem solve_original_correct_bit {n : ℕ} (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n) (ds : List (BinaryFractionalWalkOracle.Pair n)) :
    ∃ xs k charge out,
      List.Forall₂ (DemandCollection.EncodesDemand RowVertices.vertexLabel) xs ds ∧
      Run FinalDispatch.program k charge (prepare adjacency costs ds).1 [] out ∧
      FinalDispatch.Output (eraseState out).heap (eraseState out).registers.d
        (BinaryFractionalGuesses.solveInput ⟨adjacency,ds,costs⟩).1 ∧
      CorrectForInput ⟨adjacency,ds,costs⟩
        (BinaryFractionalGuesses.solveInput ⟨adjacency,ds,costs⟩).1 ∧
      (BinaryFractionalGuesses.solveInput ⟨adjacency,ds,costs⟩).1 ≠ .invalid ∧
      WordPairTableRead.Table (eraseState out).heap
        (eraseState (prepare adjacency costs ds).1).registers.a
        (IndexedRationalRead.fields costs.toList) ∧
      GraphAdjacencyProgram.Matrix (eraseState out).heap
        (eraseState (prepare adjacency costs ds).1).registers.b
        (GraphRelaxationRefinement.matrix adjacency) ∧
      DemandCollection.DemandList (eraseState out).heap
        (eraseState (prepare adjacency costs ds).1).registers.c xs ∧
      (eraseState out).registers.a=(eraseState (prepare adjacency costs ds).1).registers.a ∧
      (eraseState out).registers.b=(eraseState (prepare adjacency costs ds).1).registers.b ∧
      (eraseState out).registers.c=(eraseState (prepare adjacency costs ds).1).registers.c ∧
      out.source=[] ∧ out.stack=[] ∧ out.pc=13319 ∧ value out.next=out.heap.length ∧
      (∃ ext,(eraseState out).heap=(eraseState (prepare adjacency costs ds).1).heap++ext) ∧
      (attempt FinalDispatch.program out).result=none ∧
      (prepare adjacency costs ds).2+charge+(attempt FinalDispatch.program out).operations ≤
        preparationBound adjacency costs ds+
          completeBound 13320 (heapCells adjacency costs ds+1) (heapCells adjacency costs ds)
            (FinalDispatch.inputBound adjacency costs ds) := by
  obtain ⟨xs,k,charge,out,encoded,run,rep,table,graph,pairs,ra,rb,rc,
    source,stack,pc,dense,ext,stop,bound⟩ :=
    OriginalStoreDispatch.solve_original_bit adjacency costs ds
  have correct : CorrectForInput ⟨adjacency,ds,costs⟩
      (BinaryFractionalGuesses.solveInput ⟨adjacency,ds,costs⟩).1 :=
    BinaryFractionalGuesses.solveInput_correct ⟨adjacency,ds,costs⟩
  exact ⟨xs,k,charge,out,encoded,run,rep,correct,correct_not_invalid _ correct,
    table,graph,pairs,ra,rb,rc,source,stack,pc,dense,ext,stop,bound⟩

/-- The polynomial bound and semantic specification refer to the same returned
physical state. No equality with high-level operation counters is asserted. -/
theorem solve_original_correct_polynomial_bit {n : ℕ}
    (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (costs : BinaryFractionalRows.Row n) (ds : List (BinaryFractionalWalkOracle.Pair n)) :
    ∃ k charge out,
      Run FinalDispatch.program k charge (prepare adjacency costs ds).1 [] out ∧
      FinalDispatch.Output (eraseState out).heap (eraseState out).registers.d
        (BinaryFractionalGuesses.solveInput ⟨adjacency,ds,costs⟩).1 ∧
      CorrectForInput ⟨adjacency,ds,costs⟩
        (BinaryFractionalGuesses.solveInput ⟨adjacency,ds,costs⟩).1 ∧
      (BinaryFractionalGuesses.solveInput ⟨adjacency,ds,costs⟩).1 ≠ .invalid ∧
      out.source=[] ∧ out.stack=[] ∧ out.pc=13319 ∧ value out.next=out.heap.length ∧
      (attempt FinalDispatch.program out).result=none ∧
      (prepare adjacency costs ds).2+charge+(attempt FinalDispatch.program out).operations ≤
        OriginalStoreDispatch.totalPolynomial.eval (inputSize costs ds) := by
  obtain ⟨k,charge,out,run,rep,source,stack,pc,dense,stop,bound⟩ :=
    OriginalStoreDispatch.solve_original_polynomial_bit adjacency costs ds
  have correct : CorrectForInput ⟨adjacency,ds,costs⟩
      (BinaryFractionalGuesses.solveInput ⟨adjacency,ds,costs⟩).1 :=
    BinaryFractionalGuesses.solveInput_correct ⟨adjacency,ds,costs⟩
  exact ⟨k,charge,out,run,rep,correct,correct_not_invalid _ correct,
    source,stack,pc,dense,stop,bound⟩

end DirectedFlowCutGap.OriginalStoreCorrectness
