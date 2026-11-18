import DirectedFlowCutGap.EncodedEdgeInput

/-!
# Executing source tables with an explicit fair-bit tape

The four entry points parse and solve the graph before passing its actual
tree to the literal-bit interpreter. The completeness lemmas identify
the cut or infeasibility result and the unconsumed random suffix.
-/

namespace DirectedFlowCutGap.EncodedSourceExecution

open EncodedSolverBits FiniteDrawTrees
open BinaryArithmetic

private def runOn {A : ℕ → Type}
    (source : Option (Σ n, FiniteDrawTrees.Tree (A n))) (bits : Bits) :
    Option (Σ n, A n × Tape) := do
  let ⟨n, t⟩ ← source
  let out ← run t bits
  pure ⟨n, out⟩

private theorem runOn_complete {A : ℕ → Type} {n q : ℕ} {t : FiniteDrawTrees.Tree (A n)}
    {source : Option (Σ n, FiniteDrawTrees.Tree (A n))} (hs : source = some ⟨n, t⟩)
    (ht : Within q t) (hb : LazyFairBitTrees.Binary t) (bits : Bits) (hbits : q ≤ bits.length)
    (valid : A n → Prop) (hv : ∀ a ∈ (ideal t).support, valid a) :
    ∃ a used, runOn source bits = some ⟨n, (a, (bits.drop used, used))⟩ ∧ used ≤ q ∧ valid a := by
  obtain ⟨a, used, he, hle⟩ := complete ht hb bits hbits
  exact ⟨a, used, by simp [runOn, hs, he], hle, hv a (run_support hb he)⟩

def vertexMass (κ : ℕ) (source bits : Bits) :
    Option (Σ n, EncodedVertexSolver.Output n × Tape) :=
  runOn (EncodedVertexAmplification.sourcePolynomialBitTree κ (fun _ => EncodedWeightedRounding.tree)
    source) bits

def vertexSize (κ : ℕ) (source bits : Bits) :
    Option (Σ n, EncodedVertexSolver.Output n × Tape) :=
  runOn (EncodedVertexAmplification.sourcePolynomialBitTree κ (fun _ => EncodedSizeRounding.tree)
    source) bits

def edgeMass (κ : ℕ) (source bits : Bits) :
    Option (Σ n, EncodedEdgeSolver.Output n × Tape) :=
  runOn (EncodedEdgeInput.bitTree κ EncodedEdgeSolver.massMode source) bits

def edgeSize (κ : ℕ) (source bits : Bits) :
    Option (Σ n, EncodedEdgeSolver.Output n × Tape) :=
  runOn (EncodedEdgeInput.bitTree κ EncodedEdgeSolver.sizeMode source) bits

theorem vertexMass_complete {n : ℕ} (κ : ℕ) (D : BinaryFractionalGuesses.Input n) (bits : Bits)
    (hbits : vertexBudget κ (BinaryFractionalGuesses.decodeInput D) ≤ bits.length) :
    ∃ a used, vertexMass κ (SourcePacking.encode D.costs D.adjacency D.demands) bits =
      some ⟨n, (a, (bits.drop used, used))⟩ ∧
      used ≤ vertexBudget κ (BinaryFractionalGuesses.decodeInput D) ∧
      EncodedVertexSolver.Valid (BinaryFractionalGuesses.decodeInput D) a := by
  exact runOn_complete (EncodedVertexAmplification.sourcePolynomialBitTree_encode κ _ D)
    (vertex_mass_within κ _) (EncodedVertexAmplification.bitTree_binary ..) bits hbits _
    (fun _ ha => EncodedVertexAmplification.massBit_support_valid _ _ _ ha)

theorem vertexSize_complete {n : ℕ} (κ : ℕ) (D : BinaryFractionalGuesses.Input n) (bits : Bits)
    (hbits : vertexBudget κ (BinaryFractionalGuesses.decodeInput D) ≤ bits.length) :
    ∃ a used, vertexSize κ (SourcePacking.encode D.costs D.adjacency D.demands) bits =
      some ⟨n, (a, (bits.drop used, used))⟩ ∧
      used ≤ vertexBudget κ (BinaryFractionalGuesses.decodeInput D) ∧
      EncodedVertexSolver.Valid (BinaryFractionalGuesses.decodeInput D) a := by
  exact runOn_complete (EncodedVertexAmplification.sourcePolynomialBitTree_encode κ _ D)
    (vertex_size_within κ _) (EncodedVertexAmplification.bitTree_binary ..) bits hbits _
    (fun _ ha => EncodedVertexAmplification.sizeBit_support_valid _ _ _ ha)

theorem edgeMass_complete {n : ℕ} (κ : ℕ) (D : EncodedEdgeInput.Input n) (bits : Bits)
    (hbits : edgeBudget κ (EncodedEdgeInput.decodeInput D) ≤ bits.length) :
    ∃ a used, edgeMass κ (EncodedEdgeInput.encode D) bits = some ⟨n, (a, (bits.drop used, used))⟩ ∧
      used ≤ edgeBudget κ (EncodedEdgeInput.decodeInput D) ∧
      EncodedEdgeSolver.Valid (EncodedEdgeInput.decodeInput D) a :=
  runOn_complete (EncodedEdgeInput.bitTree_encode κ _ D) (edge_mass_within κ _)
    (EncodedEdgeSolver.bitTree_binary ..) bits hbits _
    (fun _ ha => EncodedEdgeSolver.mass_support_valid _ _ ha)

theorem edgeSize_complete {n : ℕ} (κ : ℕ) (D : EncodedEdgeInput.Input n) (bits : Bits)
    (hbits : edgeBudget κ (EncodedEdgeInput.decodeInput D) ≤ bits.length) :
    ∃ a used, edgeSize κ (EncodedEdgeInput.encode D) bits = some ⟨n, (a, (bits.drop used, used))⟩ ∧
      used ≤ edgeBudget κ (EncodedEdgeInput.decodeInput D) ∧
      EncodedEdgeSolver.Valid (EncodedEdgeInput.decodeInput D) a :=
  runOn_complete (EncodedEdgeInput.bitTree_encode κ _ D) (edge_size_within κ _)
    (EncodedEdgeSolver.bitTree_binary ..) bits hbits _
    (fun _ ha => EncodedEdgeSolver.size_support_valid _ _ ha)

end DirectedFlowCutGap.EncodedSourceExecution
