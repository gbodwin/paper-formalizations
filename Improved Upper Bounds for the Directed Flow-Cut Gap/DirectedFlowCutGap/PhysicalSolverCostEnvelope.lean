import DirectedFlowCutGap.PhysicalAmplifiedVertexCost
import DirectedFlowCutGap.PhysicalAmplifiedEdgeSolver

/-! Polynomial bounds for the counters of the amplified solvers. The
bound accepts the native draw cap and the encoded source length separately. -/

namespace DirectedFlowCutGap.PhysicalSolverCostEnvelope

open BinaryArithmetic BinaryFractionalRows BinaryRational Polynomial
open EncodedVertexAmplification ChargedPhysicalVertexSolver
open PhysicalIntegerRoundingCost (eval_mono)

private theorem fold_max_le {B : ℕ} (xs : List ℕ) (h : ∀ x ∈ xs, x ≤ B) : xs.foldr max 0 ≤ B := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons a as ih => exact max_le (h a List.mem_cons_self) (ih (fun x hx => h x (List.mem_cons_of_mem a hx)))

def rowEnvelope (n B : ℕ) : ℕ := 2*B+2*n+3

theorem rowLimit_le {n B : ℕ} (D : BinaryFractionalGuesses.Input n)
    (fits : ∀ i, StoredBounded (get D.costs i) B) :
    rowLimit (BinaryFractionalGuesses.decodeInput D) ≤ rowEnvelope n B := by
  have width : FractionalCoverRawCore.inputWidth (BinaryFractionalGuesses.decodeInput D).costs ≤ B := by
    change FractionalCoverRawCore.inputWidth (decodeRow D.costs) ≤ B
    rw [← BinaryFractionalGuesses.inputWidth_value, BinaryFractionalGuesses.inputWidth, BinaryFractionalGuesses.widthList_value]
    apply fold_max_le
    intro x hx
    obtain ⟨fraction,mem,rfl⟩ := List.mem_map.mp hx
    obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp mem
    have finite : i<n := by simpa using hi
    have hf := fits ⟨i,finite⟩
    change StoredBounded D.costs[i] B at hf
    have same : D.costs[i]=fraction := by simpa only [Vector.getElem_toList] using eq
    rw [same] at hf
    exact max_le ((Nat.size_le.mpr (value_lt fraction.num)).trans hf.1)
      ((Nat.size_le.mpr (value_lt fraction.den)).trans hf.2)
  have count : n.size ≤ n := Nat.size_le.mpr n.lt_two_pow_self
  unfold rowLimit rowEnvelope FractionalCoverGuesses.gridSteps
  omega

noncomputable def trialEnvelope : Polynomial ℕ := (X+1)*((C 4*X+C 3)*X)+1+X

theorem trialLimit_le {n B x : ℕ} (D : BinaryFractionalGuesses.Input n) (draw extra confidence : ℕ)
    (hn : n ≤ x) (hB : B ≤ x) (hd : draw ≤ x) (he : extra ≤ x) (hc : confidence ≤ x)
    (fits : ∀ i, StoredBounded (get D.costs i) B) :
    trialLimit (BinaryFractionalGuesses.decodeInput D) draw extra confidence ≤ trialEnvelope.eval x := by
  have rows := rowLimit_le D fits
  have r : rowLimit (BinaryFractionalGuesses.decodeInput D) ≤ 4*x+3 := by
    unfold rowEnvelope at rows
    omega
  apply (FairBitConfidence.trials_le ..).trans
  simp only [trialEnvelope,eval_mul,eval_add,eval_C,eval_X,eval_one]
  change (extra+1)*(rowLimit (BinaryFractionalGuesses.decodeInput D)*draw)+1+confidence ≤ _
  gcongr

/-- Bound the three observed counters, including a polynomial for the actual
number of shared rejection trials. The runner can have a different rounding
dimension, as happens when it uses the edge gadget. -/
theorem run_polynomial (q : Polynomial ℕ) : ∃ p : Polynomial ℕ,
    ∀ {n B x : ℕ} (D : BinaryFractionalGuesses.Input n) (round : PhysicalVertexSampling.Runner n)
      (draw extra confidence : ℕ) (tape : Bits),
      n ≤ x → B ≤ x → draw ≤ x → extra ≤ x → confidence ≤ x → (PhysicalSourceDispatch.input D).length ≤ x →
      1 ≤ B → (∀ i, StoredBounded (get D.costs i) B) →
      (∀ input bits (r : PhysicalIntegerRounding.Result n),
        round (trialLimit (BinaryFractionalGuesses.decodeInput D) draw extra confidence) input bits = some r →
          r.paid ≤ q.eval (trialEnvelope.eval x+x)) →
      ∀ {out : PhysicalAmplifiedVertexSolver.Result n},
      PhysicalAmplifiedVertexSolver.run D round draw extra confidence tape = some out →
        out.dispatch+out.readback+out.roundingAndSelection ≤ p.eval x := by
  let trials := trialEnvelope
  let inst := PhysicalSourceDispatch.instructionPolynomial
  let H : Polynomial ℕ := 1+inst
  let cell := C 64*(H+1)*(inst+1)
  let word := H*(cell+cell)
  let fraction := cell+word+word
  let best := C 2*cell+H*(cell+fraction)
  let lookup := C 2*cell+fraction+H*(cell+best)
  let sum := X*(C 2048*((X+1)*(X+1)+1)^2+C 4)+1
  let compare := C 2048*(X*(X+1)+C 2)^2
  let row := q.comp (trials+X)+sum+C 10+compare
  let sample := (C 4*X+C 3)*row+1+C 4*X+C 10
  let amplify := (X+1)*sample+((X+1)*sum+X*compare)+C 20*(X+1)^2+C 5
  refine ⟨PhysicalSourceDispatch.paidPolynomial+lookup+amplify,?_⟩
  intro n B x D round draw extra confidence tape hn hB hd he hc length positive fits pc out executed
  let R := q.eval (trials.eval x+x)
  obtain ⟨dispatch,readback,paid⟩ := PhysicalAmplifiedVertexCost.run_paid D round draw extra confidence R tape positive fits pc executed
  obtain ⟨dispatchLimit,readbackLimit⟩ := PhysicalSolverCharges.budgets_of_source_length D length
  have rows := rowLimit_le D fits
  have r : rowLimit (BinaryFractionalGuesses.decodeInput D) ≤ 4*x+3 := by
    unfold rowEnvelope at rows
    omega
  have rounding : budget (BinaryFractionalGuesses.decodeInput D) B extra R ≤ amplify.eval x := by
    simp only [amplify,sample,row,compare,sum,eval_mul,eval_add,eval_C,eval_X,eval_one,eval_pow,eval_comp]
    unfold budget ChargedAmplification.budget BinaryCutPriceSelection.selectionBound sampleBudget
      ChargedCutSelection.rowBound BinaryFractionalRows.sumBound
    dsimp only [R]
    gcongr
  have readEval : lookup.eval x = PhysicalCoverAccess.planBound (1+inst.eval x) (inst.eval x) := by
    simp only [lookup,best,fraction,word,cell,H,eval_mul,eval_add,eval_C,eval_one,
      PhysicalCoverAccess.planBound,PhysicalCoverAccess.bestBound,PhysicalCoverAccess.fractionBound,
      PhysicalCoverAccess.wordBound,PhysicalCoverAccess.cellBound]
  simp only [eval_add,readEval]
  exact Nat.add_le_add (Nat.add_le_add (dispatch.trans dispatchLimit) (readback.trans readbackLimit)) (paid.trans rounding)

theorem exponent_le (n κ : ℕ) : confidenceExponent n κ ≤ (n+2)*κ := by
  have log := Nat.log_le_self 2 (max 1 n)
  have size : max 1 n ≤ n+1 := max_le (by omega) (by omega)
  rw [← Nat.log2_eq_log_two] at log
  unfold confidenceExponent FairBitWords.width
  exact Nat.mul_le_mul_right κ (by omega)

noncomputable def drawPolynomial (vertices : Polynomial ℕ) : Polynomial ℕ :=
  let m := C 6*(C 4*vertices^2)
  (m^3+C 2)*(C 2*m*m)

theorem drawPolynomial_eval (v : Polynomial ℕ) (x : ℕ) :
    (drawPolynomial v).eval x = roundDrawBound (v.eval x) := by
  simp only [drawPolynomial,eval_mul,eval_add,eval_pow,eval_C,roundDrawBound,EncodedUniformRounding.drawBound]

abbrev vertexSize {n : ℕ} (D : BinaryFractionalGuesses.Input n) (κ : ℕ) : ℕ :=
  n+D.demands.length+ChargedVertexModes.priceWidth D+κ

/-- End-to-end counters in the original vertex dimension, number of demands,
stored cost bits and confidence exponent. -/
theorem vertex_polynomial : ∃ p : Polynomial ℕ, ∀ {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode)
    (D : BinaryFractionalGuesses.Input n) (tape : Bits) {out : PhysicalAmplifiedVertexSolver.Result n},
    PhysicalAmplifiedVertexSolver.vertex κ mode D tape = some out →
      out.dispatch+out.readback+out.roundingAndSelection ≤ p.eval (vertexSize D κ) := by
  obtain ⟨q,hq⟩ := PhysicalVertexRoundingCost.polynomial_bound
  obtain ⟨p,hp⟩ := run_polynomial q
  let wire := C 2*(X+X*X+X*(X+X))+C 3*(X+X+X)+C 3
  let exponent := (X+C 2)*X+1
  let pad := X+wire+exponent+drawPolynomial X
  refine ⟨p.comp pad,?_⟩
  intro n κ mode D tape out executed
  let y := vertexSize D κ
  let x := pad.eval y
  let e := confidenceExponent n κ
  let B := ChargedVertexModes.priceWidth D
  let T := trialLimit (BinaryFractionalGuesses.decodeInput D) (roundDrawBound n) e (e+1)
  have hy : y ≤ x := by
    simp only [x,pad,eval_add,eval_X]
    omega
  have hn : n ≤ y := by dsimp only [y,vertexSize]; omega
  have hB : B ≤ y := by dsimp only [B,y,vertexSize]; omega
  have hd : D.demands.length ≤ y := by dsimp only [y,vertexSize]; omega
  have hκ : κ ≤ y := by dsimp only [y,vertexSize]; omega
  have he : e+1 ≤ x := by
    have h := Nat.add_le_add_right ((exponent_le n κ).trans
      (Nat.mul_le_mul (Nat.add_le_add_right hn 2) hκ)) 1
    have hx : exponent.eval y ≤ x := by simp only [x,pad,eval_add,eval_X]; omega
    simp only [exponent,eval_add,eval_mul,eval_C,eval_X,eval_one] at hx
    exact h.trans hx
  have draw : roundDrawBound n ≤ x := by
    have hx : (drawPolynomial X).eval y ≤ x := by simp only [x,pad,eval_add,eval_X]; omega
    rw [drawPolynomial_eval,eval_X] at hx
    unfold roundDrawBound EncodedUniformRounding.drawBound at hx ⊢
    exact (show ((6*(4*n^2))^3+2)*(2*(6*(4*n^2))*(6*(4*n^2))) ≤
      ((6*(4*y^2))^3+2)*(2*(6*(4*y^2))*(6*(4*y^2))) by gcongr).trans hx
  have source : (PhysicalSourceDispatch.input D).length ≤ x := by
    have hx : wire.eval y ≤ x := by simp only [x,pad,eval_add,eval_X]; omega
    apply (PhysicalSourceSizeBounds.source_size_le D).trans
    apply le_trans ?_ hx
    simp only [wire,eval_add,eval_mul,eval_C,eval_X,PhysicalSourceSizeBounds.sourceSizeBound]
    have stored : LambdaRowProgram.rowBits D.costs.toList ≤ y := (Nat.le_add_right _ 1).trans hB
    gcongr
  have positive := ChargedVertexModes.priceWidth_positive D
  have fits := ChargedVertexModes.priceWidth_bounds D
  have eBound : e ≤ x := Nat.le_trans (Nat.le_add_right e 1) he
  have ht : T ≤ trialEnvelope.eval x+x :=
    (trialLimit_le D (roundDrawBound n) e (e+1) (hn.trans hy) (hB.trans hy) draw eBound he fits).trans (Nat.le_add_right _ _)
  let runner : PhysicalVertexSampling.Runner n :=
    match mode with | .mass => PhysicalVertexRounding.weighted | .size => PhysicalVertexRounding.size
  have paid : ∀ input bits (r : PhysicalIntegerRounding.Result n), runner T input bits = some r →
      r.paid ≤ q.eval (trialEnvelope.eval x+x) := by
    have dim : n ≤ trialEnvelope.eval x+x := (hn.trans hy).trans (Nat.le_add_left _ _)
    cases mode
    · exact (hq n T _ dim ht).1
    · exact (hq n T _ dim ht).2
  have ran : PhysicalAmplifiedVertexSolver.run D runner (roundDrawBound n) e (e+1) tape = some out := by
    cases mode <;> simpa only [PhysicalAmplifiedVertexSolver.vertex, runner, e] using executed
  rw [eval_comp]
  exact hp D runner (roundDrawBound n) e (e+1) tape (hn.trans hy) (hB.trans hy) draw eBound he source positive fits paid ran

end DirectedFlowCutGap.PhysicalSolverCostEnvelope
