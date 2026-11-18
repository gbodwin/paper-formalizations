import DirectedFlowCutGap.EncodedSourceExecution
import DirectedFlowCutGap.PhysicalSourceDispatch

/-!
# Rounding the rows read from a physical fractional dispatch

The fixed parser and fractional dispatcher consume the serialized graph.
The retained cover rows read from the terminal heap become the candidates
for rounding. The output reports the physical prefix charge separately.
-/

namespace DirectedFlowCutGap.PhysicalVertexSolver

open FiniteDrawTrees EncodedVertexSolver PhysicalCoverReader
open BinaryArithmetic RetainedGridState

private def treeFromPlan {n : ℕ} (D : GraphInput n) (round : Rounding n) :
    Plan n → FiniteDrawTrees.Tree (Output n)
  | .infeasible d => roundOutput D round (.infeasible d)
  | .zero mask => roundOutput D round (.zero (BinaryFractionalRows.column mask))
  | .invalid => roundOutput D round .invalid
  | .covers rows =>
    let candidates := rows.map (fun y => round (roundingInput D y))
    map (fun a : Option (Flags n) => a.elim .invalid .cut) (EncodedCutSelection.best D.costs candidates)

private theorem treeFromPlan_eq {n : ℕ} (D : GraphInput n) (round : Rounding n)
    (out : BinaryFractionalGuesses.Output n) :
    treeFromPlan D round (plan out) = roundOutput D round (BinaryFractionalGuesses.decodeOutput out) := by
  cases out with
  | covers rows =>
    simp only [treeFromPlan, plan, roundOutput, BinaryFractionalGuesses.decodeOutput,
      List.map_map, BinaryFractionalCore.decodeState]
    rfl
  | infeasible _ | zero _ | invalid => rfl

private def boundedFromRun {n : ℕ} (roundBound extraSamples confidence : ℕ)
    (G : GraphInput n) (round : Rounding n) (result : Option (Plan n × ℕ)) :
    Option (FiniteDrawTrees.Tree (Output n) × ℕ) :=
  let q := drawBound G roundBound
  result.map fun (p, paid) =>
    (EncodedAmplification.bitTree (EncodedVertexAmplification.codePrice G)
      (treeFromPlan G round p) q extraSamples confidence, paid)

private theorem boundedFromRun_eq {n paid : ℕ} (roundBound extraSamples confidence : ℕ)
    (D : BinaryFractionalGuesses.Input n) (round : Rounding n) {result : Option (Plan n × ℕ)}
    (h : result = some (plan (BinaryFractionalGuesses.solveInput D).1, paid)) :
    boundedFromRun roundBound extraSamples confidence (BinaryFractionalGuesses.decodeInput D) round
      result = some (EncodedVertexAmplification.boundedBitTree roundBound extraSamples confidence
        (BinaryFractionalGuesses.decodeInput D) round, paid) := by
  simp only [boundedFromRun, h, Option.map_some, treeFromPlan_eq,
    BinaryFractionalGuesses.solveInput_refines,
    EncodedVertexAmplification.boundedBitTree, EncodedVertexAmplification.boundedFromOutput]

def initializedBoundedTree {n : ℕ} (roundBound extraSamples confidence : ℕ)
    (D : BinaryFractionalGuesses.Input n) (round : Rounding n) :
    Option (FiniteDrawTrees.Tree (Output n) × ℕ) :=
  boundedFromRun roundBound extraSamples confidence (BinaryFractionalGuesses.decodeInput D)
    round (PhysicalCoverExecution.run D)

theorem initializedBoundedTree_eq {n : ℕ} (roundBound extraSamples confidence : ℕ)
    (D : BinaryFractionalGuesses.Input n) (round : Rounding n) :
    ∃ paid,
      initializedBoundedTree roundBound extraSamples confidence D round = some
        (EncodedVertexAmplification.boundedBitTree roundBound extraSamples confidence
          (BinaryFractionalGuesses.decodeInput D) round, paid) ∧
      paid ≤ OriginalStoreDispatch.totalPolynomial.eval
        (OriginalStoreInitial.inputSize D.costs D.demands) := by
  obtain ⟨paid, hr, hp⟩ := PhysicalCoverExecution.run_eq D
  exact ⟨paid, boundedFromRun_eq roundBound extraSamples confidence D round hr,
    hp.trans (PhysicalCoverExecution.budget_polynomial D)⟩

def rawTree {n : ℕ} (κ : ℕ) (D : BinaryFractionalGuesses.Input n) (round : Rounding n) (graph : Bits) :
    Option (FiniteDrawTrees.Tree (Output n) × ℕ) :=
  let e := EncodedVertexAmplification.confidenceExponent n κ
  boundedFromRun (EncodedVertexAmplification.roundDrawBound n) e (e + 1)
    (BinaryFractionalGuesses.decodeInput D) round
    (PhysicalSourceDispatch.runFrom (PhysicalSourceDispatch.steps D + 1) graph)

theorem rawTree_eq {n : ℕ} (κ : ℕ) (D : BinaryFractionalGuesses.Input n) (round : Rounding n) :
    ∃ paid,
      rawTree κ D round (PhysicalSourceDispatch.input D) = some
        (EncodedVertexAmplification.polynomialBitTree κ (BinaryFractionalGuesses.decodeInput D) round,
          paid) ∧
      paid ≤ PhysicalSourceDispatch.paidPolynomial.eval (PhysicalSourceDispatch.input D).length := by
  obtain ⟨paid, hr, hp⟩ := PhysicalSourceDispatch.run_eq D
  refine ⟨paid, ?_, hp.trans (PhysicalSourceDispatch.paidBound_polynomial D)⟩
  simpa only [rawTree, PhysicalSourceDispatch.run, EncodedVertexAmplification.polynomialBitTree,
    EncodedVertexAmplification.bitTree] using
    boundedFromRun_eq (EncodedVertexAmplification.roundDrawBound n)
      (EncodedVertexAmplification.confidenceExponent n κ)
      (EncodedVertexAmplification.confidenceExponent n κ + 1) D round hr

def runOn {A : ℕ → Type}
    (prepared : Option (Σ n, FiniteDrawTrees.Tree (A n) × ℕ)) (tape : Bits) :
    Option (Σ n, A n × EncodedSolverBits.Tape × ℕ) := do
  let ⟨n, (tree, paid)⟩ ← prepared
  let (out, suffix) ← EncodedSolverBits.run tree tape
  pure ⟨n, (out, suffix, paid)⟩

theorem runOn_complete {A : ℕ → Type} {n q paid : ℕ} {t : FiniteDrawTrees.Tree (A n)}
    {prepared : Option (Σ n, FiniteDrawTrees.Tree (A n) × ℕ)}
    (hs : prepared = some ⟨n, (t, paid)⟩)
    (ht : Within q t) (hb : LazyFairBitTrees.Binary t) (tape : Bits) (hbits : q ≤ tape.length)
    (valid : A n → Prop) (hv : ∀ a ∈ (ideal t).support, valid a) :
    ∃ a used, runOn prepared tape = some ⟨n, (a, (tape.drop used, used), paid)⟩ ∧
      used ≤ q ∧ valid a := by
  obtain ⟨a, used, he, hle⟩ := EncodedSolverBits.complete ht hb tape hbits
  exact ⟨a, used, by simp [runOn, hs, he], hle, hv a (EncodedSolverBits.run_support hb he)⟩

def prepareOn {A B : ℕ → Type} (init : (n : ℕ) → A n → Option (B n))
    (parsed : Option (Σ n, A n)) : Option (Σ n, B n) :=
  parsed.bind fun ⟨n, input⟩ => (init n input).map fun result => ⟨n, result⟩

theorem prepareOn_eq {A B : ℕ → Type} (init : (n : ℕ) → A n → Option (B n))
    {parsed : Option (Σ n, A n)} {n : ℕ} {input : A n} {result : B n}
    (hp : parsed = some ⟨n, input⟩) (hi : init n input = some result) :
    prepareOn init parsed = some ⟨n, result⟩ := by
  simp only [prepareOn, hp, Option.bind_some, hi, Option.map_some]

def sourceTree (κ : ℕ) (round : (n : ℕ) → Rounding n) (graph : Bits) :
    Option (Σ n, FiniteDrawTrees.Tree (Output n) × ℕ) :=
  prepareOn (fun n D => rawTree κ D (round n) graph) (EncodedVertexInput.parse graph)

theorem sourceTree_eq {n : ℕ} (κ : ℕ) (D : BinaryFractionalGuesses.Input n)
    (round : (n : ℕ) → Rounding n) :
    ∃ paid, sourceTree κ round (SourcePacking.encode D.costs D.adjacency D.demands) =
      some ⟨n, (EncodedVertexAmplification.polynomialBitTree κ
        (BinaryFractionalGuesses.decodeInput D) (round n), paid)⟩ ∧
      paid ≤ PhysicalSourceDispatch.paidPolynomial.eval (PhysicalSourceDispatch.input D).length := by
  obtain ⟨paid, ht, hp⟩ := rawTree_eq κ D (round n)
  exact ⟨paid, prepareOn_eq (fun n G => rawTree κ G (round n) (PhysicalSourceDispatch.input D))
    (EncodedVertexInput.parse_encode D) ht, hp⟩

def source (κ : ℕ) (round : (n : ℕ) → Rounding n) (graph tape : Bits) :
    Option (Σ n, Output n × EncodedSolverBits.Tape × ℕ) :=
  runOn (sourceTree κ round graph) tape

theorem source_complete {n : ℕ} (κ : ℕ) (D : BinaryFractionalGuesses.Input n)
    (round : (n : ℕ) → Rounding n) (tape : Bits)
    (hbits : EncodedSolverBits.vertexBudget κ (BinaryFractionalGuesses.decodeInput D) ≤ tape.length)
    (hreads : Within (EncodedSolverBits.vertexBudget κ (BinaryFractionalGuesses.decodeInput D))
      (EncodedVertexAmplification.polynomialBitTree κ (BinaryFractionalGuesses.decodeInput D) (round n)))
    (hvalid : ∀ a ∈ (ideal (EncodedVertexAmplification.polynomialBitTree κ
      (BinaryFractionalGuesses.decodeInput D) (round n))).support,
      Valid (BinaryFractionalGuesses.decodeInput D) a) :
    ∃ output used paid,
      source κ round (SourcePacking.encode D.costs D.adjacency D.demands) tape =
        some ⟨n, (output, (tape.drop used, used), paid)⟩ ∧
      used ≤ EncodedSolverBits.vertexBudget κ (BinaryFractionalGuesses.decodeInput D) ∧
      paid ≤ PhysicalSourceDispatch.paidPolynomial.eval (PhysicalSourceDispatch.input D).length ∧
      Valid (BinaryFractionalGuesses.decodeInput D) output := by
  obtain ⟨paid, ht, hp⟩ := sourceTree_eq κ D round
  have hb : LazyFairBitTrees.Binary
      (EncodedVertexAmplification.polynomialBitTree κ (BinaryFractionalGuesses.decodeInput D) (round n)) :=
    EncodedVertexAmplification.bitTree_binary
    (EncodedVertexAmplification.confidenceExponent n κ) (EncodedVertexAmplification.confidenceExponent n κ + 1)
    (BinaryFractionalGuesses.decodeInput D) (round n)
  obtain ⟨a, used, hr, hbound, ha⟩ := runOn_complete ht hreads hb tape hbits _ hvalid
  exact ⟨a, used, paid, hr, hbound, hp, ha⟩

theorem source_mass_complete {n : ℕ} (κ : ℕ) (D : BinaryFractionalGuesses.Input n)
    (tape : Bits)
    (hbits : EncodedSolverBits.vertexBudget κ (BinaryFractionalGuesses.decodeInput D) ≤ tape.length) :
    ∃ output used paid,
      source κ (fun _ => EncodedWeightedRounding.tree)
        (SourcePacking.encode D.costs D.adjacency D.demands) tape =
        some ⟨n, (output, (tape.drop used, used), paid)⟩ ∧
      used ≤ EncodedSolverBits.vertexBudget κ (BinaryFractionalGuesses.decodeInput D) ∧
      paid ≤ PhysicalSourceDispatch.paidPolynomial.eval (PhysicalSourceDispatch.input D).length ∧
      Valid (BinaryFractionalGuesses.decodeInput D) output :=
  source_complete κ D _ tape hbits (EncodedSolverBits.vertex_mass_within κ _)
    (fun _ ha => EncodedVertexAmplification.massBit_support_valid _ _ _ ha)

theorem source_size_complete {n : ℕ} (κ : ℕ) (D : BinaryFractionalGuesses.Input n)
    (tape : Bits)
    (hbits : EncodedSolverBits.vertexBudget κ (BinaryFractionalGuesses.decodeInput D) ≤ tape.length) :
    ∃ output used paid,
      source κ (fun _ => EncodedSizeRounding.tree)
        (SourcePacking.encode D.costs D.adjacency D.demands) tape =
        some ⟨n, (output, (tape.drop used, used), paid)⟩ ∧
      used ≤ EncodedSolverBits.vertexBudget κ (BinaryFractionalGuesses.decodeInput D) ∧
      paid ≤ PhysicalSourceDispatch.paidPolynomial.eval (PhysicalSourceDispatch.input D).length ∧
      Valid (BinaryFractionalGuesses.decodeInput D) output :=
  source_complete κ D _ tape hbits (EncodedSolverBits.vertex_size_within κ _)
    (fun _ ha => EncodedVertexAmplification.sizeBit_support_valid _ _ _ ha)

end DirectedFlowCutGap.PhysicalVertexSolver
