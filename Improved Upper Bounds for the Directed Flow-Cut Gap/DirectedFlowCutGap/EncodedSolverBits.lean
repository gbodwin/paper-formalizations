import DirectedFlowCutGap.EncodedEdgeSolver

/-!
# Bounded consumption of literal fair bits

The input tape is passed to the actual draw interpreter. A successful
execution returns its unconsumed suffix and the number of bits read.
-/

namespace DirectedFlowCutGap.EncodedSolverBits

open FiniteDrawTrees

abbrev Tape := List Bool × ℕ

private def bitValue (b : Bool) : Fin 2 := if b then 1 else 0

private def readBit (n : ℕ) (_ : 0 < n) : StateT Tape Option (Fin n) :=
  fun (bits, reads) =>
    match bits with
    | [] => none
    | b :: rest =>
      if h : n = 2 then some (h.symm ▸ bitValue b, (rest, reads + 1)) else none

def run {A : Type} (t : FiniteDrawTrees.Tree A) (bits : List Bool) : Option (A × Tape) :=
  (FiniteDrawTrees.execute readBit t).run (bits, 0)

private theorem step_at {A : Type} (next : Fin 2 → FiniteDrawTrees.Tree A)
    (b : Bool) (bs : List Bool) (start : ℕ) :
    (FiniteDrawTrees.execute readBit (.draw 2 (by decide) next)).run (b :: bs, start) =
      (FiniteDrawTrees.execute readBit (next (bitValue b))).run (bs, start + 1) := rfl

private theorem complete_from {A : Type} {t : FiniteDrawTrees.Tree A} {budget : ℕ}
    (h : Within budget t) (hb : LazyFairBitTrees.Binary t)
    (bs : List Bool) (hbs : budget ≤ bs.length) (start : ℕ) :
    ∃ a used, (FiniteDrawTrees.execute readBit t).run (bs, start) =
      some (a, (bs.drop used, start + used)) ∧ used ≤ budget := by
  induction h generalizing bs start with
  | pure budget a => exact ⟨a, 0, rfl, Nat.zero_le _⟩
  | @draw remaining n hn next _ ih =>
    cases hb with
    | draw hc =>
      cases bs with
      | nil => simp at hbs
      | cons b bs =>
        have ht : remaining ≤ bs.length := by simpa using hbs
        obtain ⟨a, used, hr, hused⟩ := ih (bitValue b) (hc (bitValue b)) bs ht (start + 1)
        refine ⟨a, used + 1, ?_, by omega⟩
        rw [step_at]
        simpa only [List.drop_succ_cons, Nat.add_assoc, Nat.add_comm 1] using hr

theorem complete {A : Type} {t : FiniteDrawTrees.Tree A} {budget : ℕ}
    (h : Within budget t) (hb : LazyFairBitTrees.Binary t)
    (bs : List Bool) (hbs : budget ≤ bs.length) :
    ∃ a used, run t bs = some (a, (bs.drop used, used)) ∧ used ≤ budget := by
  simpa only [run, Nat.zero_add] using complete_from h hb bs hbs 0

private theorem support_from {A : Type} {t : FiniteDrawTrees.Tree A}
    (hb : LazyFairBitTrees.Binary t) (a : A) (tape out : Tape)
    (h : (FiniteDrawTrees.execute readBit t).run tape = some (a, out)) :
    a ∈ (ideal t).support := by
  induction hb generalizing tape out with
  | pure x =>
    have hp : some (x, tape) = some (a, out) := h
    have ha : x = a := congrArg Prod.fst (Option.some.inj hp)
    subst a
    simp [ideal, law]
  | @draw next _ ih =>
    rcases tape with ⟨bits, start⟩
    cases bits with
    | nil =>
      have hf : none = some (a, out) := h
      cases hf
    | cons b bs =>
      rw [step_at] at h
      change a ∈ ((uniformDraw 2 (by decide)).bind (fun i => ideal (next i))).support
      exact (PMF.mem_support_bind_iff _ _ _).mpr
        ⟨bitValue b, PMF.mem_support_uniformOfFintype _, ih (bitValue b) _ _ h⟩

theorem run_support {A : Type} {t : FiniteDrawTrees.Tree A} (h : LazyFairBitTrees.Binary t)
    {bits : List Bool} {a : A} {rest : Tape} (hr : run t bits = some (a, rest)) :
    a ∈ (ideal t).support :=
  support_from h a (bits, 0) rest hr

private theorem width_le (n : ℕ) : FairBitWords.width n ≤ n + 1 := by
  unfold FairBitWords.width
  rw [Nat.log2_eq_log_two]
  exact Nat.add_le_add_right (Nat.log_le_self 2 n) 1

private theorem size_le (n : ℕ) : n.size ≤ n + 1 := by
  exact (Nat.size_le.mpr n.lt_two_pow_self).trans (Nat.le_succ _)

/-- A polynomial in the displayed dimensions, maximum field width and
requested confidence degree. It bounds random reads on every execution. -/
def polynomial (n dimension roundSize B κ : ℕ) : ℕ :=
  let e := (n + 2) * κ + 1
  let Q := e * ((2 * B + 2 * (dimension + 1) + 3) *
    EncodedUniformRounding.drawBound (4 * roundSize ^ 2))
  let N := 6 * (4 * roundSize ^ 2)
  Q * (Q + (e + 1)) * (N * N + 3 * (4 * roundSize ^ 2) + 1)

theorem amplifier_le_polynomial (n dimension roundSize B κ : ℕ) :
    let e := EncodedVertexAmplification.confidenceExponent n κ + 1
    let Q := e * ((FractionalCoverGuesses.gridSteps dimension B + 1) *
      EncodedUniformRounding.drawBound (4 * roundSize ^ 2))
    Q * FairBitConfidence.trials Q e * EncodedWeightedRounding.drawWidth roundSize ≤
      polynomial n dimension roundSize B κ := by
  let e := EncodedVertexAmplification.confidenceExponent n κ + 1
  let E := (n + 2) * κ + 1
  let Q := e * ((FractionalCoverGuesses.gridSteps dimension B + 1) *
    EncodedUniformRounding.drawBound (4 * roundSize ^ 2))
  let Q' := E * ((2 * B + 2 * (dimension + 1) + 3) *
    EncodedUniformRounding.drawBound (4 * roundSize ^ 2))
  have he : e ≤ E := by
    have h := width_le (max 1 n)
    have hM : max 1 n ≤ n + 1 := max_le (by omega) (by omega)
    unfold e E EncodedVertexAmplification.confidenceExponent
    gcongr
    omega
  have hq : Q ≤ Q' := by
    have hs := size_le dimension
    unfold Q Q' FractionalCoverGuesses.gridSteps
    have hh : 2 * B + 2 * dimension.size + 2 + 1 ≤ 2 * B + 2 * (dimension + 1) + 3 := by omega
    gcongr
  have ht := FairBitConfidence.trials_le Q e
  have hw : EncodedWeightedRounding.drawWidth roundSize ≤
      (6 * (4 * roundSize ^ 2)) * (6 * (4 * roundSize ^ 2)) + 3 * (4 * roundSize ^ 2) + 1 := by
    unfold EncodedWeightedRounding.drawWidth RetainedDrawTrees.sampleWidth
    apply (width_le _).trans
    exact Nat.add_le_add_right (max_le (by omega) (by omega)) 1
  have hf : FairBitConfidence.trials Q e ≤ Q' + (E + 1) := by omega
  exact Nat.mul_le_mul (Nat.mul_le_mul hq hf) hw

def vertexBudget {n : ℕ} (κ : ℕ) (D : EncodedVertexSolver.GraphInput n) : ℕ :=
  polynomial n n n (FractionalCoverRawCore.inputWidth D.costs) κ

theorem vertex_mass_within {n : ℕ} (κ : ℕ) (D : EncodedVertexSolver.GraphInput n) :
    Within (vertexBudget κ D)
      (EncodedVertexAmplification.polynomialBitTree κ D EncodedWeightedRounding.tree) :=
  within_mono (EncodedVertexAmplification.polynomialBit_within κ D _
    EncodedWeightedRounding.tree_within EncodedWeightedRounding.tree_widths)
    (amplifier_le_polynomial n n n _ κ)

theorem vertex_size_within {n : ℕ} (κ : ℕ) (D : EncodedVertexSolver.GraphInput n) :
    Within (vertexBudget κ D)
      (EncodedVertexAmplification.polynomialBitTree κ D EncodedSizeRounding.tree) :=
  within_mono (EncodedVertexAmplification.polynomialBit_within κ D _
    EncodedSizeRounding.tree_within EncodedSizeRounding.tree_widths)
    (amplifier_le_polynomial n n n _ κ)

def edgeBudget {n : ℕ} (κ : ℕ) (D : EncodedEdgeLineInput.Input n) : ℕ :=
  polynomial n (EncodedEdgeLineInput.lineSize n) (2 * n * (n + 4))
    (FractionalCoverRawCore.inputWidth (EncodedEdgeLineInput.lineInput D).costs) κ

theorem polynomial_roundSize_mono {n v a b B κ : ℕ} (h : a ≤ b) :
    polynomial n v a B κ ≤ polynomial n v b B κ := by
  dsimp only [polynomial, EncodedUniformRounding.drawBound]
  gcongr

theorem edge_mass_within {n : ℕ} (κ : ℕ) (D : EncodedEdgeLineInput.Input n) :
    Within (edgeBudget κ D) (EncodedEdgeSolver.bitTree κ D EncodedEdgeSolver.massMode) := by
  apply within_mono (EncodedEdgeSolver.bitTree_within κ D _
    (fun _ => EncodedWeightedRounding.tree_within) (fun _ => EncodedWeightedRounding.tree_widths))
  have h : 2 * n * (n.log2 + 4) ≤ 2 * n * (n + 4) := by
    have hl : n.log2 ≤ n := by rw [Nat.log2_eq_log_two]; exact Nat.log_le_self 2 n
    gcongr
  exact (amplifier_le_polynomial n (EncodedEdgeLineInput.lineSize n) _ _ κ).trans
    (polynomial_roundSize_mono h)

theorem edge_size_within {n : ℕ} (κ : ℕ) (D : EncodedEdgeLineInput.Input n) :
    Within (edgeBudget κ D) (EncodedEdgeSolver.bitTree κ D EncodedEdgeSolver.sizeMode) := by
  apply within_mono (EncodedEdgeSolver.bitTree_within κ D _
    (fun _ => EncodedSizeRounding.tree_within) (fun _ => EncodedSizeRounding.tree_widths))
  have h : 2 * n * (n.log2 + 4) ≤ 2 * n * (n + 4) := by
    have hl : n.log2 ≤ n := by rw [Nat.log2_eq_log_two]; exact Nat.log_le_self 2 n
    gcongr
  exact (amplifier_le_polynomial n (EncodedEdgeLineInput.lineSize n) _ _ κ).trans
    (polynomial_roundSize_mono h)

end DirectedFlowCutGap.EncodedSolverBits
