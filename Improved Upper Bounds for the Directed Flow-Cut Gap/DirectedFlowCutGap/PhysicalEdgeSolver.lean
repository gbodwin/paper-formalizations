import DirectedFlowCutGap.PhysicalVertexSolver

/-!
# Physical fractional solving for the original edge input

The typed line graph has a binary encoding of its exact rational costs.
The same physical dispatcher computes the fractional rows on that graph.
Dyadic rounding and cut selection use the original graph and costs.
-/

namespace DirectedFlowCutGap.PhysicalEdgeSolver

open BinaryArithmetic FiniteDrawTrees EncodedEdgeLineInput
open RawNonnegativeRational

private def fraction (q : Code) : BinaryRational.Fraction :=
  ⟨q.num.bits, q.den.bits, by rw [value_bits]; exact q.positive_den⟩

@[simp] private theorem decode_fraction (q : Code) : BinaryRational.decode (fraction q) = q := by
  cases q
  simp [BinaryRational.decode, fraction, value_bits]

private theorem decode_row {m : ℕ} (c : FractionalCoverRawCore.RawRow m) :
    BinaryFractionalRows.decodeRow (c.map fraction) = c := by
  apply Vector.ext
  intro i hi
  simp [BinaryFractionalRows.decodeRow, BinaryFractionalRows.get]

def binaryLineInput {n : ℕ} (D : Input n) : BinaryFractionalGuesses.Input (lineSize n) :=
  let line := lineInput D
  ⟨line.adjacency, line.demands, line.costs.map fraction⟩

@[simp] theorem decode_binaryLineInput {n : ℕ} (D : Input n) :
    BinaryFractionalGuesses.decodeInput (binaryLineInput D) = lineInput D := by
  simp only [binaryLineInput, BinaryFractionalGuesses.decodeInput, decode_row]

private theorem rowWidth_le (xs : List BinaryRational.Fraction) (w : ℕ)
    (hw : ∀ r ∈ xs, r.num.length + r.den.length ≤ w) :
    LambdaRowProgram.rowBits xs ≤ xs.length * w := by
  induction xs with
  | nil => simp [LambdaRowProgram.rowBits]
  | cons r rs ih =>
    have h := hw r (List.mem_cons_self ..)
    have hs := ih (fun r hr => hw r (List.mem_cons_of_mem _ hr))
    simp only [LambdaRowProgram.rowBits, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

def lineInputSizeBound (n demands B : ℕ) : ℕ :=
  lineSize n + demands + lineSize n * (2 * B) + 1

theorem line_size_le {n B : ℕ} (D : Input n) (hB : 1 ≤ B)
    (hc : ∀ u v : Fin n, (D.costs[u.val][v.val]).num.size ≤ B ∧
      (D.costs[u.val][v.val]).den.size ≤ B) :
    OriginalStoreInitial.inputSize (binaryLineInput D).costs (binaryLineInput D).demands ≤
      lineInputSizeBound n D.demands.length B := by
  let row := (binaryLineInput D).costs.toList
  have hr : ∀ r ∈ row, r.num.length + r.den.length ≤ 2 * B := by
    intro r hr
    obtain ⟨i, hi, hri⟩ := List.mem_iff_getElem.mp hr
    have hi' : i < lineSize n := by simpa [row] using hi
    rw [← hri]
    simp only [row, Vector.getElem_toList, binaryLineInput, Vector.getElem_map]
    change (fraction (FractionalCoverRawCore.get (lineInput D).costs ⟨i, hi'⟩)).num.length +
      (fraction (FractionalCoverRawCore.get (lineInput D).costs ⟨i, hi'⟩)).den.length ≤ 2 * B
    have hw := lineInput_cost_width D hB hc ⟨i, hi'⟩
    simp only [fraction, Nat.size_eq_bits_len, two_mul]
    exact Nat.add_le_add hw.1 hw.2
  have hs := rowWidth_le row (2 * B) hr
  simp only [row, Vector.length_toList] at hs
  have hd : (binaryLineInput D).demands.length = D.demands.length := by simp [binaryLineInput, lineInput]
  unfold OriginalStoreInitial.inputSize lineInputSizeBound
  rw [hd]
  exact Nat.add_le_add_right (Nat.add_le_add_left hs _) 1

private theorem eval_mono (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval_add] using Nat.add_le_add hp hq
  | monomial n c =>
    rw [Polynomial.eval_monomial, Polynomial.eval_monomial]
    gcongr

def paidBound {n : ℕ} (D : Input n) : ℕ :=
  PhysicalCoverExecution.budget (binaryLineInput D)

theorem paidBound_polynomial {n : ℕ} (D : Input n) :
    paidBound D ≤ OriginalStoreDispatch.totalPolynomial.eval
      (OriginalStoreInitial.inputSize (binaryLineInput D).costs (binaryLineInput D).demands) :=
  PhysicalCoverExecution.budget_polynomial _

theorem paidBound_original {n B : ℕ} (D : Input n) (hB : 1 ≤ B)
    (hc : ∀ u v : Fin n, (D.costs[u.val][v.val]).num.size ≤ B ∧
      (D.costs[u.val][v.val]).den.size ≤ B) :
    paidBound D ≤ OriginalStoreDispatch.totalPolynomial.eval (lineInputSizeBound n D.demands.length B) :=
  (paidBound_polynomial D).trans
    (eval_mono OriginalStoreDispatch.totalPolynomial (line_size_le D hB hc))

def initializedTree {n : ℕ} (κ : ℕ) (D : Input n) (mode : EncodedEdgeSolver.Mode) :
    Option (FiniteDrawTrees.Tree (EncodedEdgeSolver.Output n) × ℕ) :=
  let e := EncodedVertexAmplification.confidenceExponent n κ
  (PhysicalVertexSolver.initializedBoundedTree (EncodedEdgeSolver.drawBound n)
    e (e + 1) (binaryLineInput D) (EncodedEdgeSolver.round D mode)).map fun (tree, paid) =>
      (map (EncodedEdgeSolver.outputFor D) tree, paid)

theorem initializedTree_eq {n : ℕ} (κ : ℕ) (D : Input n) (mode : EncodedEdgeSolver.Mode) :
    ∃ paid, initializedTree κ D mode = some (EncodedEdgeSolver.bitTree κ D mode, paid) ∧
      paid ≤ OriginalStoreDispatch.totalPolynomial.eval
        (OriginalStoreInitial.inputSize (binaryLineInput D).costs (binaryLineInput D).demands) := by
  obtain ⟨p, hp, hb⟩ := PhysicalVertexSolver.initializedBoundedTree_eq (EncodedEdgeSolver.drawBound n)
    (EncodedVertexAmplification.confidenceExponent n κ)
    (EncodedVertexAmplification.confidenceExponent n κ + 1) (binaryLineInput D) (EncodedEdgeSolver.round D mode)
  refine ⟨p, ?_, hb⟩
  simp only [initializedTree, hp, Option.map_some, EncodedEdgeSolver.bitTree, decode_binaryLineInput]

def sourceTree (κ : ℕ) (mode : EncodedEdgeSolver.Mode) (graph : Bits) :
    Option (Σ n, FiniteDrawTrees.Tree (EncodedEdgeSolver.Output n) × ℕ) :=
  PhysicalVertexSolver.prepareOn
    (fun _ D => initializedTree κ (EncodedEdgeInput.decodeInput D) mode)
    (EncodedEdgeInput.parse graph)

theorem sourceTree_eq {n : ℕ} (κ : ℕ) (D : EncodedEdgeInput.Input n) (mode : EncodedEdgeSolver.Mode) :
    let line := binaryLineInput (EncodedEdgeInput.decodeInput D)
    ∃ paid, sourceTree κ mode (EncodedEdgeInput.encode D) =
      some ⟨n, (EncodedEdgeSolver.bitTree κ (EncodedEdgeInput.decodeInput D) mode, paid)⟩ ∧
      paid ≤ OriginalStoreDispatch.totalPolynomial.eval (OriginalStoreInitial.inputSize line.costs line.demands) := by
  obtain ⟨paid, ht, hp⟩ := initializedTree_eq κ (EncodedEdgeInput.decodeInput D) mode
  exact ⟨paid, PhysicalVertexSolver.prepareOn_eq
    (fun _ G => initializedTree κ (EncodedEdgeInput.decodeInput G) mode) (EncodedEdgeInput.parse_encode D) ht, hp⟩

def source (κ : ℕ) (mode : EncodedEdgeSolver.Mode) (source tape : Bits) :
    Option (Σ n, EncodedEdgeSolver.Output n × EncodedSolverBits.Tape × ℕ) :=
  PhysicalVertexSolver.runOn (sourceTree κ mode source) tape

theorem source_complete {n : ℕ} (κ : ℕ) (D : EncodedEdgeInput.Input n)
    (mode : EncodedEdgeSolver.Mode) (tape : Bits)
    (hbits : EncodedSolverBits.edgeBudget κ (EncodedEdgeInput.decodeInput D) ≤ tape.length)
    (hreads : Within (EncodedSolverBits.edgeBudget κ (EncodedEdgeInput.decodeInput D))
      (EncodedEdgeSolver.bitTree κ (EncodedEdgeInput.decodeInput D) mode))
    (hvalid : ∀ a ∈ (ideal (EncodedEdgeSolver.bitTree κ (EncodedEdgeInput.decodeInput D) mode)).support,
      EncodedEdgeSolver.Valid (EncodedEdgeInput.decodeInput D) a) :
    let line := binaryLineInput (EncodedEdgeInput.decodeInput D)
    ∃ output used paid,
      source κ mode (EncodedEdgeInput.encode D) tape =
        some ⟨n, (output, (tape.drop used, used), paid)⟩ ∧
      used ≤ EncodedSolverBits.edgeBudget κ (EncodedEdgeInput.decodeInput D) ∧
      paid ≤ OriginalStoreDispatch.totalPolynomial.eval
        (OriginalStoreInitial.inputSize line.costs line.demands) ∧
      EncodedEdgeSolver.Valid (EncodedEdgeInput.decodeInput D) output := by
  obtain ⟨paid, ht, hp⟩ := sourceTree_eq κ D mode
  have hb := EncodedEdgeSolver.bitTree_binary κ (EncodedEdgeInput.decodeInput D) mode
  obtain ⟨a, used, hr, hbound, ha⟩ := PhysicalVertexSolver.runOn_complete ht hreads hb tape hbits _ hvalid
  exact ⟨a, used, paid, hr, hbound, hp, ha⟩

theorem source_mass_complete {n : ℕ} (κ : ℕ) (D : EncodedEdgeInput.Input n) (tape : Bits)
    (hbits : EncodedSolverBits.edgeBudget κ (EncodedEdgeInput.decodeInput D) ≤ tape.length) :
    let line := binaryLineInput (EncodedEdgeInput.decodeInput D)
    ∃ output used paid,
      source κ EncodedEdgeSolver.massMode (EncodedEdgeInput.encode D) tape =
        some ⟨n, (output, (tape.drop used, used), paid)⟩ ∧
      used ≤ EncodedSolverBits.edgeBudget κ (EncodedEdgeInput.decodeInput D) ∧
      paid ≤ OriginalStoreDispatch.totalPolynomial.eval
        (OriginalStoreInitial.inputSize line.costs line.demands) ∧
      EncodedEdgeSolver.Valid (EncodedEdgeInput.decodeInput D) output :=
  source_complete κ D _ tape hbits (EncodedSolverBits.edge_mass_within κ _)
    (fun _ ha => EncodedEdgeSolver.mass_support_valid _ _ ha)

theorem source_size_complete {n : ℕ} (κ : ℕ) (D : EncodedEdgeInput.Input n) (tape : Bits)
    (hbits : EncodedSolverBits.edgeBudget κ (EncodedEdgeInput.decodeInput D) ≤ tape.length) :
    let line := binaryLineInput (EncodedEdgeInput.decodeInput D)
    ∃ output used paid,
      source κ EncodedEdgeSolver.sizeMode (EncodedEdgeInput.encode D) tape =
        some ⟨n, (output, (tape.drop used, used), paid)⟩ ∧
      used ≤ EncodedSolverBits.edgeBudget κ (EncodedEdgeInput.decodeInput D) ∧
      paid ≤ OriginalStoreDispatch.totalPolynomial.eval
        (OriginalStoreInitial.inputSize line.costs line.demands) ∧
      EncodedEdgeSolver.Valid (EncodedEdgeInput.decodeInput D) output :=
  source_complete κ D _ tape hbits (EncodedSolverBits.edge_size_within κ _)
    (fun _ ha => EncodedEdgeSolver.size_support_valid _ _ ha)

end DirectedFlowCutGap.PhysicalEdgeSolver
