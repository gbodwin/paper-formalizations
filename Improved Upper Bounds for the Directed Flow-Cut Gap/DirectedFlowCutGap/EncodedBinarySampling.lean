import DirectedFlowCutGap.BinaryDrawTreeExecution
import DirectedFlowCutGap.EncodedSolverBits

/-!
# Binary sampler charges in the amplified vertex and edge solvers

The additional observation records modeled binary sampler operations.
The projected finite tree is the same amplified solver, including its
minimum selection and bounded-rejection defaults. Other deterministic
work in the solver has a separate cost.
-/

namespace DirectedFlowCutGap.EncodedBinarySampling

open FiniteDrawTrees LazyFairBitTrees BinaryDrawTreeExecution

def amplified {A : Type} (price : A → RawNonnegativeRational.Code)
    (tree : DrawTree A) (Q extra confidence : ℕ) : DrawTree (A × ℕ) :=
  BinaryDrawTreeExecution.run (FairBitConfidence.trials ((extra + 1) * Q) confidence)
    (EncodedAmplification.selectedTree price tree extra)

theorem amplified_value {A : Type} (price : A → RawNonnegativeRational.Code)
    (tree : DrawTree A) (Q extra confidence : ℕ) :
    map Prod.fst (amplified price tree Q extra confidence) =
      EncodedAmplification.bitTree price tree Q extra confidence :=
  run_value _ _

def polynomial (reads : ℕ) : ℕ :=
  reads * oneDrawBound reads reads

private theorem charge_le {Q T width reads : ℕ} (hT : 0 < T) (hw : 0 < width)
    (hr : Q * T * width ≤ reads) : Q * oneDrawBound T width ≤ polynomial reads := by
  by_cases hzero : Q = 0
  · simp [hzero]
  have hQ : 0 < Q := Nat.pos_of_ne_zero hzero
  have hcounts : Q ≤ reads := by
    have hp := Nat.mul_le_mul (Nat.mul_le_mul (le_refl Q) (show 1 ≤ T from hT)) (show 1 ≤ width from hw)
    have h : Q ≤ Q * T * width := by simpa only [Nat.mul_one] using hp
    exact h.trans hr
  have htrials : T ≤ reads := by
    have hp := Nat.mul_le_mul (Nat.mul_le_mul (show 1 ≤ Q from hQ) (le_refl T)) (show 1 ≤ width from hw)
    have h : T ≤ Q * T * width := by simpa only [Nat.one_mul, Nat.mul_one] using hp
    exact h.trans hr
  have hwidth : width ≤ reads := by
    have hp := Nat.mul_le_mul (Nat.mul_le_mul (show 1 ≤ Q from hQ) (show 1 ≤ T from hT)) (le_refl width)
    have h : width ≤ Q * T * width := by simpa only [Nat.one_mul] using hp
    exact h.trans hr
  unfold polynomial oneDrawBound
  gcongr

theorem amplified_cost {A : Type} {tree : DrawTree A} {Q width reads : ℕ}
    (price : A → RawNonnegativeRational.Code) (extra confidence : ℕ)
    (ht : Within Q tree) (hw : WidthsLE width tree) (hwidth : 0 < width)
    (hb : (extra + 1) * Q * FairBitConfidence.trials ((extra + 1) * Q) confidence * width ≤ reads)
    {out : A × ℕ} (ho : out ∈ (ideal (amplified price tree Q extra confidence)).support) :
    out.2 ≤ polynomial reads := by
  have hs := within_map (EncodedAmplification.samples_within ht (extra + 1))
    (EncodedAmplification.minimum price extra)
  have hsw := widths_map (EncodedAmplification.samples_widths hw (extra + 1))
    (EncodedAmplification.minimum price extra)
  have htrials : 0 < FairBitConfidence.trials ((extra + 1) * Q) confidence := by
    unfold FairBitConfidence.trials
    have := FairBitWords.width_pos ((extra + 1) * Q)
    omega
  exact (run_cost hs hsw _ ho).trans (charge_le htrials hwidth hb)

open EncodedVertexSolver EncodedVertexAmplification

def vertex {n : ℕ} (κ : ℕ) (D : GraphInput n) (round : Rounding n) :
    DrawTree (Output n × ℕ) :=
  let e := confidenceExponent n κ
  amplified (codePrice D) (tree D round) (drawBound D (roundDrawBound n)) e (e + 1)

theorem vertex_value {n : ℕ} (κ : ℕ) (D : GraphInput n) (round : Rounding n) :
    map Prod.fst (vertex κ D round) = polynomialBitTree κ D round :=
  amplified_value ..

private theorem positive_drawWidth (n : ℕ) : 0 < EncodedWeightedRounding.drawWidth n :=
  FairBitWords.width_pos _

theorem vertex_cost {n : ℕ} (κ : ℕ) (D : GraphInput n) (round : Rounding n)
    (hround : ∀ r : RoundingInput n, Within (roundDrawBound n) (round r))
    (hwidth : ∀ r : RoundingInput n, WidthsLE (EncodedWeightedRounding.drawWidth n) (round r))
    {out : Output n × ℕ} (ho : out ∈ (ideal (vertex κ D round)).support) :
    out.2 ≤ polynomial (EncodedSolverBits.vertexBudget κ D) :=
  amplified_cost _ _ _ (tree_within D round _ hround) (tree_widths D round hwidth)
    (positive_drawWidth _) (EncodedSolverBits.amplifier_le_polynomial n n n _ κ) ho

open EncodedEdgeLineInput

private def edgeBeforeProjection {n : ℕ} (κ : ℕ) (D : Input n) (mode : EncodedEdgeSolver.Mode) :
    DrawTree (EncodedVertexSolver.Output (lineSize n) × ℕ) :=
  let G := lineInput D
  let e := confidenceExponent n κ
  amplified (codePrice G) (tree G (EncodedEdgeSolver.round D mode))
    (drawBound G (EncodedEdgeSolver.drawBound n)) e (e + 1)

def edge {n : ℕ} (κ : ℕ) (D : Input n) (mode : EncodedEdgeSolver.Mode) :
    DrawTree (EncodedEdgeSolver.Output n × ℕ) :=
  map (fun (a, q) => (EncodedEdgeSolver.outputFor D a, q)) (edgeBeforeProjection κ D mode)

private theorem map_charge_projection {A B : Type} (f : A → B) (t : DrawTree (A × ℕ)) :
    map Prod.fst (map (fun (a, q) => (f a, q)) t) = map f (map Prod.fst t) := by
  change Prod.fst <$> ((fun (a, q) => (f a, q)) <$> t) = f <$> (Prod.fst <$> t)
  simp only [Functor.map_map]

theorem edge_value {n : ℕ} (κ : ℕ) (D : Input n) (mode : EncodedEdgeSolver.Mode) :
    map Prod.fst (edge κ D mode) = EncodedEdgeSolver.bitTree κ D mode := by
  simp only [edge, map_charge_projection, edgeBeforeProjection, amplified_value,
    EncodedEdgeSolver.bitTree, boundedBitTree, boundedFromOutput, tree]

private theorem edge_cap_le {n : ℕ} (κ : ℕ) (D : Input n) :
    EncodedSolverBits.polynomial n (lineSize n) (2 * n * (Nat.log2 n + 4))
      (FractionalCoverRawCore.inputWidth (lineInput D).costs) κ ≤ EncodedSolverBits.edgeBudget κ D := by
  have hl : n.log2 ≤ n := by rw [Nat.log2_eq_log_two]; exact Nat.log_le_self 2 n
  apply EncodedSolverBits.polynomial_roundSize_mono
  gcongr

theorem edge_cost {n : ℕ} (κ : ℕ) (D : Input n) (mode : EncodedEdgeSolver.Mode)
    (hmode : ∀ m (I : EncodedUnitCostReplication.Input m),
      Within (EncodedUniformRounding.drawBound (4 * m ^ 2)) (mode m I))
    (hwidth : ∀ m (I : EncodedUnitCostReplication.Input m),
      WidthsLE (EncodedWeightedRounding.drawWidth m) (mode m I))
    {out : EncodedEdgeSolver.Output n × ℕ} (ho : out ∈ (ideal (edge κ D mode)).support) :
    out.2 ≤ polynomial (EncodedSolverBits.edgeBudget κ D) := by
  let f (a : EncodedVertexSolver.Output (lineSize n) × ℕ) := (EncodedEdgeSolver.outputFor D a.1, a.2)
  have he : ideal (edge κ D mode) = (ideal (edgeBeforeProjection κ D mode)).map f :=
    law_map uniformDraw f (edgeBeforeProjection κ D mode)
  have hm : out ∈ ((ideal (edgeBeforeProjection κ D mode)).map f).support := he ▸ ho
  obtain ⟨a, ha, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hm
  exact amplified_cost _ _ _
    (tree_within (lineInput D) (EncodedEdgeSolver.round D mode) _ (EncodedEdgeSolver.round_within D mode hmode))
    (tree_widths (lineInput D) (EncodedEdgeSolver.round D mode) (EncodedEdgeSolver.round_widths D mode hwidth))
    (positive_drawWidth (2 * n * (Nat.log2 n + 4)))
    ((EncodedSolverBits.amplifier_le_polynomial n (lineSize n) _ _ κ).trans (edge_cap_le κ D))
    ha

theorem vertex_mass_cost {n : ℕ} (κ : ℕ) (D : GraphInput n) {out : Output n × ℕ}
    (ho : out ∈ (ideal (vertex κ D EncodedWeightedRounding.tree)).support) :
    out.2 ≤ polynomial (EncodedSolverBits.vertexBudget κ D) :=
  vertex_cost κ D _ EncodedWeightedRounding.tree_within EncodedWeightedRounding.tree_widths ho

theorem vertex_size_cost {n : ℕ} (κ : ℕ) (D : GraphInput n) {out : Output n × ℕ}
    (ho : out ∈ (ideal (vertex κ D EncodedSizeRounding.tree)).support) :
    out.2 ≤ polynomial (EncodedSolverBits.vertexBudget κ D) :=
  vertex_cost κ D _ EncodedSizeRounding.tree_within EncodedSizeRounding.tree_widths ho

theorem edge_mass_cost {n : ℕ} (κ : ℕ) (D : Input n) {out : EncodedEdgeSolver.Output n × ℕ}
    (ho : out ∈ (ideal (edge κ D EncodedEdgeSolver.massMode)).support) :
    out.2 ≤ polynomial (EncodedSolverBits.edgeBudget κ D) :=
  edge_cost κ D _ (fun _ => EncodedWeightedRounding.tree_within)
    (fun _ => EncodedWeightedRounding.tree_widths) ho

theorem edge_size_cost {n : ℕ} (κ : ℕ) (D : Input n) {out : EncodedEdgeSolver.Output n × ℕ}
    (ho : out ∈ (ideal (edge κ D EncodedEdgeSolver.sizeMode)).support) :
    out.2 ≤ polynomial (EncodedSolverBits.edgeBudget κ D) :=
  edge_cost κ D _ (fun _ => EncodedSizeRounding.tree_within)
    (fun _ => EncodedSizeRounding.tree_widths) ho

end DirectedFlowCutGap.EncodedBinarySampling
