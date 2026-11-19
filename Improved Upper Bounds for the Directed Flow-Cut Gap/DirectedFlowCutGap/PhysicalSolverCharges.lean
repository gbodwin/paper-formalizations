import DirectedFlowCutGap.PhysicalSourceReadback
import DirectedFlowCutGap.PhysicalVertexSolver
import DirectedFlowCutGap.PhysicalEdgeSolver
import DirectedFlowCutGap.EncodedBinarySampling

/-!
# A source solver with charges from the same run

The vertex pipeline reads the physical retained rows once. It samples
the amplified rounding tree with the binary arithmetic sampler and
returns the exact unused random suffix. The three charges account for
physical dispatch, terminal heap lookups and binary sampling.
-/

namespace DirectedFlowCutGap.PhysicalSolverCharges

open BinaryArithmetic FiniteDrawTrees LazyFairBitTrees
open EncodedVertexSolver EncodedVertexAmplification

structure Charges where
  dispatch : ℕ
  lookups : ℕ
  sampling : ℕ

private theorem within_of_map {A B : Type} {f : A → B} {t : FiniteDrawTrees.Tree A}
    {q : ℕ} (h : Within q (map f t)) : Within q t := by
  induction t generalizing q with
  | pure x => exact .pure q x
  | draw n hn next ih =>
    change Within q (.draw n hn (fun j => map f (next j))) at h
    cases h with
    | draw children => exact .draw (fun j => ih j (children j))

private theorem binary_of_map {A B : Type} {f : A → B} {t : FiniteDrawTrees.Tree A}
    (h : Binary (map f t)) : Binary t := by
  induction t with
  | pure x => exact .pure x
  | draw n hn next ih =>
    change Binary (.draw n hn (fun j => map f (next j))) at h
    cases h with
    | draw children => exact .draw (fun j => ih j (children j))

private def runOn {A : ℕ → Type}
    (ready : Option (Σ n, FiniteDrawTrees.Tree (A n × ℕ) × ℕ × ℕ)) (tape : Bits) :
    Option (Σ n, A n × EncodedSolverBits.Tape × Charges) := do
  let ⟨n, (t, paid, read)⟩ ← ready
  let ((out, sampling), suffix) ← EncodedSolverBits.run t tape
  pure ⟨n, (out, suffix, ⟨paid, read, sampling⟩)⟩

private def forgetCharges {A : ℕ → Type} :
    (Σ n, A n × EncodedSolverBits.Tape × Charges) → (Σ n, A n × EncodedSolverBits.Tape)
  | ⟨n, (out, suffix, _)⟩ => ⟨n, (out, suffix)⟩

private theorem runOn_value {A : ℕ → Type} {n dispatch lookups : ℕ}
    {tree : FiniteDrawTrees.Tree (A n × ℕ)} {plain : FiniteDrawTrees.Tree (A n)}
    {ready : Option (Σ n, FiniteDrawTrees.Tree (A n × ℕ) × ℕ × ℕ)}
    (hp : ready = some ⟨n, (tree, dispatch, lookups)⟩)
    (he : map Prod.fst tree = plain) (tape : Bits) :
    (runOn ready tape).map forgetCharges =
      (EncodedSolverBits.run plain tape).map (fun out => ⟨n, out⟩) := by
  rw [← he, EncodedSolverBits.run_map, hp]
  cases ht : EncodedSolverBits.run tree tape with
  | none => simp [runOn, ht]
  | some result =>
    rcases result with ⟨⟨out, charge⟩, suffix⟩
    simp [runOn, ht, forgetCharges]

private theorem runOn_fairTape {A : ℕ → Type} {n budget dispatch lookups : ℕ}
    {tree : FiniteDrawTrees.Tree (A n × ℕ)} {plain : FiniteDrawTrees.Tree (A n)}
    {ready : Option (Σ n, FiniteDrawTrees.Tree (A n × ℕ) × ℕ × ℕ)}
    (hp : ready = some ⟨n, (tree, dispatch, lookups)⟩)
    (he : map Prod.fst tree = plain) (hw : Within budget plain) (hb : Binary plain) :
    (EncodedSolverBits.fairTape budget).map (fun tape =>
      (runOn ready tape).map (fun ⟨m, (out, _, _)⟩ => (⟨m, out⟩ : Σ m, A m))) =
    (ideal plain).map (fun out => some (⟨n, out⟩ : Σ m, A m)) := by
  have hr (tape : Bits) := congrArg
    (Option.map (fun ⟨m, (out, _)⟩ => (⟨m, out⟩ : Σ m, A m))) (runOn_value hp he tape)
  simp only [Option.map_map, Function.comp_def, forgetCharges] at hr
  simp only [hr]
  have h := congrArg (PMF.map (Option.map (fun out => (⟨n, out⟩ : Σ m, A m))))
    (EncodedSolverBits.run_fairTape hw hb)
  simpa only [PMF.map_comp, Option.map_map, Function.comp_def, Option.map_some] using h

private theorem runOn_complete {A : ℕ → Type} {n budget dispatch lookups samplerBound : ℕ}
    {tree : FiniteDrawTrees.Tree (A n × ℕ)} {plain : FiniteDrawTrees.Tree (A n)}
    {ready : Option (Σ n, FiniteDrawTrees.Tree (A n × ℕ) × ℕ × ℕ)}
    (hp : ready = some ⟨n, (tree, dispatch, lookups)⟩)
    (he : map Prod.fst tree = plain) (hw : Within budget plain) (hb : Binary plain)
    (tape : Bits) (ht : budget ≤ tape.length)
    (valid : A n → Prop) (hv : ∀ out ∈ (ideal plain).support, valid out)
    (hs : ∀ out ∈ (ideal tree).support, out.2 ≤ samplerBound) :
    ∃ out used sampled,
      runOn ready tape = some ⟨n, (out, (tape.drop used, used), ⟨dispatch, lookups, sampled⟩)⟩ ∧
      used ≤ budget ∧ sampled ≤ samplerBound ∧ valid out := by
  have htree : Within budget tree := within_of_map (he.symm ▸ hw)
  have hbinary : Binary tree := binary_of_map (he.symm ▸ hb)
  obtain ⟨⟨a, sampled⟩, used, hr, hle⟩ := EncodedSolverBits.complete htree hbinary tape ht
  have hvalue := EncodedSolverBits.run_support hbinary hr
  have hmap : ideal plain = (ideal tree).map Prod.fst := he ▸ law_map uniformDraw Prod.fst tree
  have ha : a ∈ (ideal plain).support := by
    rw [hmap]
    exact (PMF.mem_support_map_iff _ _ _).2 ⟨(a, sampled), hvalue, rfl⟩
  exact ⟨a, used, sampled, by simp [runOn, hp, hr], hle, hs _ hvalue, hv _ ha⟩

noncomputable def dispatchBudget {n : ℕ} (D : BinaryFractionalGuesses.Input n) : ℕ :=
  PhysicalSourceDispatch.paidPolynomial.eval (PhysicalSourceDispatch.input D).length

noncomputable def lookupBudget {n : ℕ} (D : BinaryFractionalGuesses.Input n) : ℕ :=
  let bound := PhysicalSourceDispatch.instructionPolynomial.eval (PhysicalSourceDispatch.input D).length
  PhysicalCoverAccess.planBound (1 + bound) bound

def treeFromPlan {n : ℕ} (roundBound extra confidence : ℕ) (G : GraphInput n)
    (round : Rounding n) (p : PhysicalCoverReader.Plan n) : FiniteDrawTrees.Tree (Output n × ℕ) :=
  EncodedBinarySampling.amplified (codePrice G) (PhysicalVertexSolver.treeFromPlan G round p)
    (drawBound G roundBound) extra confidence

def prepare {n : ℕ} (roundBound extra confidence : ℕ) (D : BinaryFractionalGuesses.Input n)
    (round : Rounding n) : Option (FiniteDrawTrees.Tree (Output n × ℕ) × ℕ × ℕ) :=
  let G := BinaryFractionalGuesses.decodeInput D
  (PhysicalSourceReadback.run D).map fun (p, charged, lookup) =>
    (treeFromPlan roundBound extra confidence G round p, charged, lookup)

theorem prepare_eq {n : ℕ} (roundBound extra confidence : ℕ) (D : BinaryFractionalGuesses.Input n)
    (round : Rounding n) :
    let G := BinaryFractionalGuesses.decodeInput D
    ∃ charged lookup,
      prepare roundBound extra confidence D round = some
        (EncodedBinarySampling.amplified (codePrice G) (tree G round)
          (drawBound G roundBound) extra confidence, charged, lookup) ∧
      charged ≤ dispatchBudget D ∧ lookup ≤ lookupBudget D := by
  obtain ⟨charged, lookup, hr, hp, hl⟩ := PhysicalSourceReadback.run_eq D
  refine ⟨charged, lookup, ?_, hp, hl⟩
  simp only [prepare, treeFromPlan, hr, Option.map_some, PhysicalVertexSolver.treeFromPlan_eq,
    BinaryFractionalGuesses.solveInput_refines, tree]

private def vertexPreparation {n : ℕ} (κ : ℕ) (D : BinaryFractionalGuesses.Input n)
    (round : Rounding n) : Option (FiniteDrawTrees.Tree (Output n × ℕ) × ℕ × ℕ) :=
  let e := confidenceExponent n κ
  prepare (roundDrawBound n) e (e + 1) D round

private def vertexTree (κ : ℕ) (round : (n : ℕ) → Rounding n) (source : Bits) :
    Option (Σ n, FiniteDrawTrees.Tree (Output n × ℕ) × ℕ × ℕ) :=
  PhysicalVertexSolver.prepareOn (fun n D => vertexPreparation κ D (round n))
    (EncodedVertexInput.parse source)

private theorem vertexTree_eq {n : ℕ} (κ : ℕ) (D : BinaryFractionalGuesses.Input n)
    (round : (n : ℕ) → Rounding n) {source : Bits} (hp : EncodedVertexInput.parse source = some ⟨n, D⟩) :
    ∃ charged lookup,
      vertexTree κ round source = some ⟨n,
        (EncodedBinarySampling.vertex κ (BinaryFractionalGuesses.decodeInput D) (round n), charged, lookup)⟩ ∧
      charged ≤ dispatchBudget D ∧ lookup ≤ lookupBudget D := by
  obtain ⟨charged, lookup, hr, hd, hl⟩ := prepare_eq (roundDrawBound n)
    (confidenceExponent n κ) (confidenceExponent n κ + 1) D (round n)
  exact ⟨charged, lookup, PhysicalVertexSolver.prepareOn_eq
      (fun n G => vertexPreparation κ G (round n)) hp hr, hd, hl⟩

def vertex (κ : ℕ) (round : (n : ℕ) → Rounding n) (source tape : Bits) :
    Option (Σ n, Output n × EncodedSolverBits.Tape × Charges) :=
  runOn (vertexTree κ round source) tape

theorem vertex_value {n : ℕ} (κ : ℕ) (D : BinaryFractionalGuesses.Input n)
    (round : (n : ℕ) → Rounding n) (source tape : Bits)
    (hp : EncodedVertexInput.parse source = some ⟨n, D⟩) :
    (vertex κ round source tape).map (fun ⟨m, (out, suffix, _)⟩ =>
      (⟨m, (out, suffix)⟩ : Σ m, Output m × EncodedSolverBits.Tape)) =
    (EncodedSolverBits.run (polynomialBitTree κ (BinaryFractionalGuesses.decodeInput D) (round n))
      tape).map (fun out => ⟨n, out⟩) := by
  obtain ⟨_, _, htree, _, _⟩ := vertexTree_eq κ D round hp
  exact runOn_value htree (EncodedBinarySampling.vertex_value κ _ (round n)) tape

theorem vertex_fairTape {n : ℕ} (κ : ℕ) (D : BinaryFractionalGuesses.Input n)
    (round : (n : ℕ) → Rounding n) (source : Bits)
    (hp : EncodedVertexInput.parse source = some ⟨n, D⟩)
    (hround : ∀ r : RoundingInput n, Within (roundDrawBound n) (round n r))
    (hwidth : ∀ r : RoundingInput n, WidthsLE (EncodedWeightedRounding.drawWidth n) (round n r)) :
    let G := BinaryFractionalGuesses.decodeInput D
    (EncodedSolverBits.fairTape (EncodedSolverBits.vertexBudget κ G)).map (fun tape =>
      (vertex κ round source tape).map (fun ⟨m, (out, _, _)⟩ => (⟨m, out⟩ : Σ m, Output m))) =
    (ideal (polynomialBitTree κ G (round n))).map (fun out => some (⟨n, out⟩ : Σ m, Output m)) := by
  let G := BinaryFractionalGuesses.decodeInput D
  obtain ⟨_, _, htree, _, _⟩ := vertexTree_eq κ D round hp
  have hw : Within (EncodedSolverBits.vertexBudget κ G) (polynomialBitTree κ G (round n)) :=
    within_mono (polynomialBit_within κ G _ hround hwidth)
      (EncodedSolverBits.amplifier_le_polynomial n n n _ κ)
  exact runOn_fairTape htree (EncodedBinarySampling.vertex_value κ G (round n)) hw
    (bitTree_binary (confidenceExponent n κ) (confidenceExponent n κ + 1) G (round n))

theorem vertex_complete {n : ℕ} (κ : ℕ) (D : BinaryFractionalGuesses.Input n)
    (round : (n : ℕ) → Rounding n) (source tape : Bits)
    (hp : EncodedVertexInput.parse source = some ⟨n, D⟩)
    (hbits : EncodedSolverBits.vertexBudget κ (BinaryFractionalGuesses.decodeInput D) ≤ tape.length)
    (hround : ∀ r : RoundingInput n, Within (roundDrawBound n) (round n r))
    (hwidth : ∀ r : RoundingInput n, WidthsLE (EncodedWeightedRounding.drawWidth n) (round n r))
    (hv : ∀ out ∈ (ideal (polynomialBitTree κ (BinaryFractionalGuesses.decodeInput D) (round n))).support,
      Valid (BinaryFractionalGuesses.decodeInput D) out) :
    ∃ out used charges,
      vertex κ round source tape = some ⟨n, (out, (tape.drop used, used), charges)⟩ ∧
      used ≤ EncodedSolverBits.vertexBudget κ (BinaryFractionalGuesses.decodeInput D) ∧
      charges.dispatch ≤ dispatchBudget D ∧ charges.lookups ≤ lookupBudget D ∧
      charges.sampling ≤ EncodedBinarySampling.polynomial
        (EncodedSolverBits.vertexBudget κ (BinaryFractionalGuesses.decodeInput D)) ∧
      Valid (BinaryFractionalGuesses.decodeInput D) out := by
  let G := BinaryFractionalGuesses.decodeInput D
  obtain ⟨charged, lookup, htree, hd, hl⟩ := vertexTree_eq κ D round hp
  have hwithin : Within (EncodedSolverBits.vertexBudget κ G) (polynomialBitTree κ G (round n)) :=
    within_mono (polynomialBit_within κ G _ hround hwidth)
      (EncodedSolverBits.amplifier_le_polynomial n n n _ κ)
  have hb : Binary (polynomialBitTree κ G (round n)) :=
    bitTree_binary (confidenceExponent n κ) (confidenceExponent n κ + 1) G (round n)
  obtain ⟨out, used, sampler, hr, hu, hs, hv'⟩ :=
    runOn_complete htree (EncodedBinarySampling.vertex_value κ G (round n)) hwithin hb tape hbits _
      hv (fun _ hm => EncodedBinarySampling.vertex_cost κ G (round n) hround hwidth hm)
  exact ⟨out, used, ⟨charged, lookup, sampler⟩, hr, hu, hd, hl, hs, hv'⟩

theorem vertex_mass_complete {n : ℕ} (κ : ℕ) (D : BinaryFractionalGuesses.Input n) (source tape : Bits)
    (hp : EncodedVertexInput.parse source = some ⟨n, D⟩)
    (hbits : EncodedSolverBits.vertexBudget κ (BinaryFractionalGuesses.decodeInput D) ≤ tape.length) :
    let G := BinaryFractionalGuesses.decodeInput D
    ∃ out used charges,
      vertex κ (fun _ => EncodedWeightedRounding.tree) source tape =
        some ⟨n, (out, (tape.drop used, used), charges)⟩ ∧
      used ≤ EncodedSolverBits.vertexBudget κ G ∧
      charges.dispatch ≤ dispatchBudget D ∧ charges.lookups ≤ lookupBudget D ∧
      charges.sampling ≤ EncodedBinarySampling.polynomial (EncodedSolverBits.vertexBudget κ G) ∧ Valid G out :=
  vertex_complete κ D _ source tape hp hbits EncodedWeightedRounding.tree_within EncodedWeightedRounding.tree_widths
    (fun _ ha => massBit_support_valid _ _ _ ha)

theorem vertex_size_complete {n : ℕ} (κ : ℕ) (D : BinaryFractionalGuesses.Input n) (source tape : Bits)
    (hp : EncodedVertexInput.parse source = some ⟨n, D⟩)
    (hbits : EncodedSolverBits.vertexBudget κ (BinaryFractionalGuesses.decodeInput D) ≤ tape.length) :
    let G := BinaryFractionalGuesses.decodeInput D
    ∃ out used charges,
      vertex κ (fun _ => EncodedSizeRounding.tree) source tape =
        some ⟨n, (out, (tape.drop used, used), charges)⟩ ∧
      used ≤ EncodedSolverBits.vertexBudget κ G ∧
      charges.dispatch ≤ dispatchBudget D ∧ charges.lookups ≤ lookupBudget D ∧
      charges.sampling ≤ EncodedBinarySampling.polynomial (EncodedSolverBits.vertexBudget κ G) ∧ Valid G out :=
  vertex_complete κ D _ source tape hp hbits EncodedSizeRounding.tree_within EncodedSizeRounding.tree_widths
    (fun _ ha => sizeBit_support_valid _ _ _ ha)

open EncodedEdgeLineInput

private def edgePreparation {n : ℕ} (κ : ℕ) (D : Input n) (mode : EncodedEdgeSolver.Mode) :
    Option (FiniteDrawTrees.Tree (EncodedEdgeSolver.Output n × ℕ) × ℕ × ℕ) :=
  let e := confidenceExponent n κ
  (prepare (EncodedEdgeSolver.drawBound n) e (e + 1) (PhysicalEdgeSolver.binaryLineInput D)
    (EncodedEdgeSolver.round D mode)).map fun (tree, paid, lookups) =>
      (map (fun (out, sampling) => (EncodedEdgeSolver.outputFor D out, sampling)) tree, paid, lookups)

private theorem edgePreparation_eq {n : ℕ} (κ : ℕ) (D : Input n) (mode : EncodedEdgeSolver.Mode) :
    let line := PhysicalEdgeSolver.binaryLineInput D
    ∃ paid lookups, edgePreparation κ D mode = some (EncodedBinarySampling.edge κ D mode, paid, lookups) ∧
      paid ≤ dispatchBudget line ∧ lookups ≤ lookupBudget line := by
  obtain ⟨paid, lookups, hr, hp, hl⟩ := prepare_eq (EncodedEdgeSolver.drawBound n)
    (confidenceExponent n κ) (confidenceExponent n κ + 1) (PhysicalEdgeSolver.binaryLineInput D)
    (EncodedEdgeSolver.round D mode)
  refine ⟨paid, lookups, ?_, hp, hl⟩
  simp only [edgePreparation, hr, Option.map_some, PhysicalEdgeSolver.decode_binaryLineInput]
  rfl

private def edgeTree (κ : ℕ) (mode : EncodedEdgeSolver.Mode) (source : Bits) :
    Option (Σ n, FiniteDrawTrees.Tree (EncodedEdgeSolver.Output n × ℕ) × ℕ × ℕ) :=
  PhysicalVertexSolver.prepareOn (fun _ D => edgePreparation κ (EncodedEdgeInput.decodeInput D) mode)
    (EncodedEdgeInput.parse source)

private theorem edgeTree_eq {n : ℕ} (κ : ℕ) (D : EncodedEdgeInput.Input n)
    (mode : EncodedEdgeSolver.Mode) {source : Bits} (hp : EncodedEdgeInput.parse source = some ⟨n, D⟩) :
    let line := PhysicalEdgeSolver.binaryLineInput (EncodedEdgeInput.decodeInput D)
    ∃ paid lookup,
      edgeTree κ mode source = some ⟨n, (EncodedBinarySampling.edge κ (EncodedEdgeInput.decodeInput D) mode, paid, lookup)⟩ ∧
      paid ≤ dispatchBudget line ∧ lookup ≤ lookupBudget line := by
  obtain ⟨paid, lookup, ht, hd, hl⟩ := edgePreparation_eq κ (EncodedEdgeInput.decodeInput D) mode
  exact ⟨paid, lookup, PhysicalVertexSolver.prepareOn_eq
    (fun _ G => edgePreparation κ (EncodedEdgeInput.decodeInput G) mode) hp ht, hd, hl⟩

def edge (κ : ℕ) (mode : EncodedEdgeSolver.Mode) (source tape : Bits) :
    Option (Σ n, EncodedEdgeSolver.Output n × EncodedSolverBits.Tape × Charges) :=
  runOn (edgeTree κ mode source) tape

theorem edge_value {n : ℕ} (κ : ℕ) (D : EncodedEdgeInput.Input n)
    (mode : EncodedEdgeSolver.Mode) (source tape : Bits) (hp : EncodedEdgeInput.parse source = some ⟨n, D⟩) :
    (edge κ mode source tape).map (fun ⟨m, (out, suffix, _)⟩ =>
      (⟨m, (out, suffix)⟩ : Σ m, EncodedEdgeSolver.Output m × EncodedSolverBits.Tape)) =
    (EncodedSolverBits.run (EncodedEdgeSolver.bitTree κ (EncodedEdgeInput.decodeInput D) mode)
      tape).map (fun out => ⟨n, out⟩) := by
  obtain ⟨_, _, htree, _, _⟩ := edgeTree_eq κ D mode hp
  exact runOn_value htree (EncodedBinarySampling.edge_value κ _ mode) tape

theorem edge_fairTape {n : ℕ} (κ : ℕ) (D : EncodedEdgeInput.Input n)
    (mode : EncodedEdgeSolver.Mode) (source : Bits) (hp : EncodedEdgeInput.parse source = some ⟨n, D⟩)
    (hw : Within (EncodedSolverBits.edgeBudget κ (EncodedEdgeInput.decodeInput D))
      (EncodedEdgeSolver.bitTree κ (EncodedEdgeInput.decodeInput D) mode)) :
    let G := EncodedEdgeInput.decodeInput D
    (EncodedSolverBits.fairTape (EncodedSolverBits.edgeBudget κ G)).map (fun tape =>
      (edge κ mode source tape).map (fun ⟨m, (out, _, _)⟩ => (⟨m, out⟩ : Σ m, EncodedEdgeSolver.Output m))) =
    (ideal (EncodedEdgeSolver.bitTree κ G mode)).map (fun out => some (⟨n, out⟩ : Σ m, EncodedEdgeSolver.Output m)) := by
  obtain ⟨_, _, htree, _, _⟩ := edgeTree_eq κ D mode hp
  exact runOn_fairTape htree (EncodedBinarySampling.edge_value κ _ mode) hw (EncodedEdgeSolver.bitTree_binary κ _ mode)

theorem edge_complete {n : ℕ} (κ : ℕ) (D : EncodedEdgeInput.Input n)
    (mode : EncodedEdgeSolver.Mode) (source tape : Bits)
    (hp : EncodedEdgeInput.parse source = some ⟨n, D⟩)
    (hbits : EncodedSolverBits.edgeBudget κ (EncodedEdgeInput.decodeInput D) ≤ tape.length)
    (hwithin : Within (EncodedSolverBits.edgeBudget κ (EncodedEdgeInput.decodeInput D))
      (EncodedEdgeSolver.bitTree κ (EncodedEdgeInput.decodeInput D) mode))
    (hmode : ∀ m (I : EncodedUnitCostReplication.Input m),
      Within (EncodedUniformRounding.drawBound (4 * m ^ 2)) (mode m I))
    (hwidth : ∀ m (I : EncodedUnitCostReplication.Input m),
      WidthsLE (EncodedWeightedRounding.drawWidth m) (mode m I))
    (hv : ∀ out ∈ (ideal (EncodedEdgeSolver.bitTree κ (EncodedEdgeInput.decodeInput D) mode)).support,
      EncodedEdgeSolver.Valid (EncodedEdgeInput.decodeInput D) out) :
    let line := PhysicalEdgeSolver.binaryLineInput (EncodedEdgeInput.decodeInput D)
    ∃ out used charges,
      edge κ mode source tape = some ⟨n, (out, (tape.drop used, used), charges)⟩ ∧
      used ≤ EncodedSolverBits.edgeBudget κ (EncodedEdgeInput.decodeInput D) ∧
      charges.dispatch ≤ dispatchBudget line ∧ charges.lookups ≤ lookupBudget line ∧
      charges.sampling ≤ EncodedBinarySampling.polynomial (EncodedSolverBits.edgeBudget κ (EncodedEdgeInput.decodeInput D)) ∧
      EncodedEdgeSolver.Valid (EncodedEdgeInput.decodeInput D) out := by
  let G := EncodedEdgeInput.decodeInput D
  obtain ⟨paid, lookup, htree, hd, hl⟩ := edgeTree_eq κ D mode hp
  obtain ⟨out, used, sampler, hr, hu, hs, hv'⟩ :=
    runOn_complete htree (EncodedBinarySampling.edge_value κ G mode) hwithin
      (EncodedEdgeSolver.bitTree_binary κ G mode) tape hbits _
      hv (fun _ hm => EncodedBinarySampling.edge_cost κ G mode hmode hwidth hm)
  exact ⟨out, used, ⟨paid, lookup, sampler⟩, hr, hu, hd, hl, hs, hv'⟩

theorem edge_mass_complete {n : ℕ} (κ : ℕ) (D : EncodedEdgeInput.Input n) (source tape : Bits)
    (hp : EncodedEdgeInput.parse source = some ⟨n, D⟩)
    (hbits : EncodedSolverBits.edgeBudget κ (EncodedEdgeInput.decodeInput D) ≤ tape.length) :
    let G := EncodedEdgeInput.decodeInput D
    let line := PhysicalEdgeSolver.binaryLineInput G
    ∃ out used charges,
      edge κ EncodedEdgeSolver.massMode source tape =
        some ⟨n, (out, (tape.drop used, used), charges)⟩ ∧
      used ≤ EncodedSolverBits.edgeBudget κ G ∧
      charges.dispatch ≤ dispatchBudget line ∧ charges.lookups ≤ lookupBudget line ∧
      charges.sampling ≤ EncodedBinarySampling.polynomial (EncodedSolverBits.edgeBudget κ G) ∧
      EncodedEdgeSolver.Valid G out :=
  edge_complete κ D _ source tape hp hbits (EncodedSolverBits.edge_mass_within κ _)
    (fun _ => EncodedWeightedRounding.tree_within) (fun _ => EncodedWeightedRounding.tree_widths)
    (fun _ ha => EncodedEdgeSolver.mass_support_valid _ _ ha)

theorem edge_size_complete {n : ℕ} (κ : ℕ) (D : EncodedEdgeInput.Input n) (source tape : Bits)
    (hp : EncodedEdgeInput.parse source = some ⟨n, D⟩)
    (hbits : EncodedSolverBits.edgeBudget κ (EncodedEdgeInput.decodeInput D) ≤ tape.length) :
    let G := EncodedEdgeInput.decodeInput D
    let line := PhysicalEdgeSolver.binaryLineInput G
    ∃ out used charges,
      edge κ EncodedEdgeSolver.sizeMode source tape =
        some ⟨n, (out, (tape.drop used, used), charges)⟩ ∧
      used ≤ EncodedSolverBits.edgeBudget κ G ∧
      charges.dispatch ≤ dispatchBudget line ∧ charges.lookups ≤ lookupBudget line ∧
      charges.sampling ≤ EncodedBinarySampling.polynomial (EncodedSolverBits.edgeBudget κ G) ∧
      EncodedEdgeSolver.Valid G out :=
  edge_complete κ D _ source tape hp hbits (EncodedSolverBits.edge_size_within κ _)
    (fun _ => EncodedSizeRounding.tree_within) (fun _ => EncodedSizeRounding.tree_widths)
    (fun _ ha => EncodedEdgeSolver.size_support_valid _ _ ha)

end DirectedFlowCutGap.PhysicalSolverCharges
