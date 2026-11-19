import DirectedFlowCutGap.PhysicalBinaryVertexRounding
import DirectedFlowCutGap.PhysicalSolverCostEnvelope
import DirectedFlowCutGap.PhysicalOriginalInputCompleteness
import DirectedFlowCutGap.PhysicalWireCostEnvelope

/-! Run the original vertex solver with measured binary preparation on every
realized cover row. The output and the remaining literal tape are unchanged. -/

namespace DirectedFlowCutGap.PhysicalAmplifiedBinaryVertex

open BinaryArithmetic FiniteDrawTrees Polynomial
open EncodedVertexAmplification
open ChargedPhysicalVertexSolver (trialLimit)
open PhysicalAmplifiedVertexSolver (Result)
open PhysicalSolverCostEnvelope (vertexSize trialEnvelope trialLimit_le drawPolynomial drawPolynomial_eval exponent_le)
open PhysicalIntegerRoundingCost (eval_mono)
open PhysicalBinaryVertexRounding (sizeBudget weightedBudget)
open VertexReductionWidths (InputFits)

def runner {n : ℕ} (mode : ChargedVertexModes.Mode) : PhysicalVertexSampling.Runner n :=
  match mode with
  | .mass => fun T D tape => (PhysicalBinaryVertexRounding.weighted T D tape).map PhysicalBinaryVertexRounding.Result.charge
  | .size => fun T D tape => (PhysicalBinaryVertexRounding.size T D tape).map PhysicalBinaryVertexRounding.Result.charge

theorem runner_observe {n : ℕ} (mode : ChargedVertexModes.Mode) (T : ℕ)
    (D : EncodedUnitCostReplication.Input n) (tape : Bits) :
    (runner mode T D tape).map PhysicalIntegerRounding.Result.observe =
      LiteralTapeComposition.execute T (ChargedVertexModes.round n mode D) tape := by
  cases mode with
  | mass =>
    have h := congrArg (Option.map PhysicalIntegerRounding.Result.observe)
      (PhysicalBinaryVertexRounding.weighted_cut T D tape)
    have same := h.trans (PhysicalVertexRounding.weighted_observe T D tape)
    simpa only [runner,ChargedVertexModes.round,Option.map_map,Function.comp_def,PhysicalBinaryVertexRounding.Result.charge,
      PhysicalIntegerRounding.Result.observe] using same
  | size =>
    have h := congrArg (Option.map PhysicalIntegerRounding.Result.observe)
      (PhysicalBinaryVertexRounding.size_cut T D tape)
    have same := h.trans (PhysicalVertexRounding.size_observe T D tape)
    simpa only [runner,ChargedVertexModes.round,Option.map_map,Function.comp_def,PhysicalBinaryVertexRounding.Result.charge,
      PhysicalIntegerRounding.Result.observe] using same

def vertex {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode) (D : BinaryFractionalGuesses.Input n)
    (tape : Bits) : Option (Result n) :=
  let e := confidenceExponent n κ
  PhysicalAmplifiedVertexSolver.run D (runner mode) (roundDrawBound n) e (e+1) tape

theorem vertex_observe {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode) (D : BinaryFractionalGuesses.Input n)
    (tape : Bits) :
    (vertex κ mode D tape).map Result.observe =
      (PhysicalAmplifiedVertexSolver.vertex κ mode D tape).map Result.observe := by
  rw [PhysicalAmplifiedVertexSolver.vertex_observe]
  exact PhysicalAmplifiedVertexSolver.run_observe D _ _ _ _ _ tape (runner_observe mode)

def vertexWithCost (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits) :
    PhysicalCoverAccess.Read (Σ n,Result n) :=
  let parsed := ChargedSourceAssembly.vertex source
  (PhysicalVertexSolver.prepareOn (fun _ input => vertex κ mode input tape) parsed.1,parsed.2)

theorem vertex_complete {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode) (D : BinaryFractionalGuesses.Input n)
    (source tape : Bits) (parsed : EncodedVertexInput.parse source=some ⟨n,D⟩)
    (enough : EncodedSolverBits.vertexBudget κ (BinaryFractionalGuesses.decodeInput D) ≤ tape.length) :
    ∃ r used, (vertexWithCost κ mode source tape).1=some ⟨n,r⟩ ∧ r.suffix=tape.drop used ∧
      used ≤ EncodedSolverBits.vertexBudget κ (BinaryFractionalGuesses.decodeInput D) ∧
      EncodedVertexSolver.Valid (BinaryFractionalGuesses.decodeInput D) r.output := by
  let G := BinaryFractionalGuesses.decodeInput D
  let tree := polynomialBitTree κ G (ChargedVertexModes.round n mode)
  have legal : ∀ a ∈ (ideal tree).support, EncodedVertexSolver.Valid G a := by
    cases mode
    · exact fun _ h => massBit_support_valid _ _ _ h
    · exact fun _ h => sizeBit_support_valid _ _ _ h
  have within : Within (EncodedSolverBits.vertexBudget κ G) tree := by
    cases mode
    · exact EncodedSolverBits.vertex_mass_within κ G
    · exact EncodedSolverBits.vertex_size_within κ G
  have observe := (vertex_observe κ mode D tape).trans (PhysicalAmplifiedVertexSolver.vertex_observe κ mode D tape)
  obtain ⟨r,k,execute,rest,used,valid⟩ := PhysicalOriginalInputCompleteness.returns Result.output Result.suffix
    (vertex κ mode D tape) (EncodedVertexSolver.Valid G) observe legal within (bitTree_binary ..) enough
  have entry : (vertexWithCost κ mode source tape).1=some ⟨n,r⟩ := by
    simp only [vertexWithCost,ChargedSourceAssembly.vertex_value]
    exact PhysicalVertexSolver.prepareOn_eq (fun _ input => vertex κ mode input tape) parsed execute
  exact ⟨r,k,entry,rest,used,valid⟩

theorem vertex_fairTape {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode) (D : BinaryFractionalGuesses.Input n) :
    let G := BinaryFractionalGuesses.decodeInput D
    (EncodedSolverBits.fairTape (EncodedSolverBits.vertexBudget κ G)).map
      (fun tape => (vertex κ mode D tape).map Result.output) =
      (ideal (polynomialBitTree κ G (ChargedVertexModes.round n mode))).map some := by
  dsimp only
  have output : (fun tape => (vertex κ mode D tape).map Result.output) =
      (fun tape => (PhysicalAmplifiedVertexSolver.vertex κ mode D tape).map Result.output) := by
    funext tape
    have same := congrArg (Option.map Prod.fst) (vertex_observe κ mode D tape)
    simpa only [Option.map_map,Function.comp_def,Result.observe] using same
  rw [output]
  exact PhysicalOriginalInputSolvers.vertex_fairTape κ mode D

noncomputable def arithmeticPolynomial : Polynomial ℕ :=
  sizeBudget X (X+1+PhysicalSourceDispatch.instructionPolynomial)

theorem arithmeticPolynomial_eval (x : ℕ) :
    arithmeticPolynomial.eval x=sizeBudget x (x+1+PhysicalSourceDispatch.instructionPolynomial.eval x) := by
  simp only [arithmeticPolynomial, sizeBudget,weightedBudget,PhysicalBinaryVertexRounding.uniformBudget,
    BinaryHeavyPreparation.budget,BinaryCubeThreshold.budget,BinaryCubeThreshold.testBudget,BinaryPortPreparation.portBudget,
    BinaryVertexReductionArithmetic.reductionBudget,BinaryVertexReductionArithmetic.aggregateWidth,
    BinaryVertexReductionArithmetic.normalizedWidth,BinaryUniformArithmetic.budget,VertexReductionWidths.uniformWidth,
    BinaryIntegerCutoff.budget,BinaryEpochParameters.budget,BinaryEpochParameters.setupWidth,
    BinaryEpochParameters.logBudget,BinaryEpochParameters.logStepBudget,
    BinaryRawRational.budget,eval_add,eval_mul,eval_pow,eval_X,eval_one,eval_ofNat]

theorem runner_paid {n b T y : ℕ} (q : Polynomial ℕ)
    (qBound : ∀ n T x, n ≤ x → T ≤ x →
      (∀ (D : EncodedUnitCostReplication.Input n) tape (r : PhysicalIntegerRounding.Result n),
        PhysicalVertexRounding.weighted T D tape=some r → r.paid ≤ q.eval x) ∧
      (∀ (D : EncodedUnitCostReplication.Input n) tape (r : PhysicalIntegerRounding.Result n),
        PhysicalVertexRounding.size T D tape=some r → r.paid ≤ q.eval x))
    (mode : ChargedVertexModes.Mode) (D : EncodedUnitCostReplication.Input n) (bits : Bits)
    (fits : InputFits D b) (hn : n ≤ y) (ht : T ≤ y)
    (width : b ≤ y+1+PhysicalSourceDispatch.instructionPolynomial.eval y)
    {r : PhysicalIntegerRounding.Result n} (ran : runner mode T D bits=some r) :
    r.paid ≤ (q+arithmeticPolynomial).eval y := by
  have monotone := PhysicalBinaryVertexRounding.sizeBudget_mono hn width
  rw [eval_add,arithmeticPolynomial_eval]
  cases mode with
  | mass =>
    obtain ⟨out,call,rfl⟩ := Option.map_eq_some_iff.mp ran
    have out' := congrArg (Option.map PhysicalBinaryVertexRounding.Result.cut) call
    rw [PhysicalBinaryVertexRounding.weighted_cut,Option.map_some] at out'
    have graph := (qBound n T y hn ht).1 D bits out.cut out'
    have a := PhysicalBinaryVertexRounding.weighted_paid T D fits bits call
    have raised : weightedBudget n b ≤ weightedBudget n (b+1) :=
      PhysicalBinaryVertexRounding.weightedBudget_mono (Nat.le_refl n) (Nat.le_succ b)
    have incl : weightedBudget n (b+1) ≤ sizeBudget n b := Nat.le_add_left _ _
    exact Nat.add_le_add graph (a.trans (raised.trans (incl.trans monotone)))
  | size =>
    obtain ⟨out,call,rfl⟩ := Option.map_eq_some_iff.mp ran
    have out' := congrArg (Option.map PhysicalBinaryVertexRounding.Result.cut) call
    rw [PhysicalBinaryVertexRounding.size_cut,Option.map_some] at out'
    exact Nat.add_le_add ((qBound n T y hn ht).2 D bits out.cut out')
      ((PhysicalBinaryVertexRounding.size_paid T D fits bits call).trans monotone)

theorem vertex_polynomial : ∃ p : Polynomial ℕ, ∀ {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode)
    (D : BinaryFractionalGuesses.Input n) (tape : Bits) {out : Result n}, vertex κ mode D tape=some out →
      out.dispatch+out.readback+out.roundingAndSelection ≤ p.eval (vertexSize D κ) := by
  obtain ⟨q,hq⟩ := PhysicalVertexRoundingCost.polynomial_bound
  obtain ⟨p,hp⟩ := PhysicalSolverCostEnvelope.run_polynomial_on_rows (q+arithmeticPolynomial)
  let wire : Polynomial ℕ := 2*(X+X*X+X*(X+X))+3*(X+X+X)+3
  let exponent : Polynomial ℕ := (X+2)*X+1
  let pad := X+wire+exponent+drawPolynomial X
  refine ⟨p.comp pad,?_⟩
  intro n κ mode D tape out ran
  let y := vertexSize D κ
  let x := pad.eval y
  let z := trialEnvelope.eval x+x
  let e := confidenceExponent n κ
  let B := ChargedVertexModes.priceWidth D
  let T := trialLimit (BinaryFractionalGuesses.decodeInput D) (roundDrawBound n) e (e+1)
  have hy : y ≤ x := by simp only [x,pad,eval_add,eval_X]; omega
  have hx : x ≤ z := Nat.le_add_left _ _
  have hn : n ≤ y := by dsimp only [y,vertexSize]; omega
  have hb : B ≤ y := by dsimp only [B,y,vertexSize]; omega
  have hd : D.demands.length ≤ y := by dsimp only [y,vertexSize]; omega
  have hκ : κ ≤ y := by dsimp only [y,vertexSize]; omega
  have he : e+1 ≤ x := by
    have h := Nat.add_le_add_right ((exponent_le n κ).trans (Nat.mul_le_mul (Nat.add_le_add_right hn 2) hκ)) 1
    have hx' : exponent.eval y ≤ x := by simp only [x,pad,eval_add,eval_X]; omega
    simp only [exponent,eval_add,eval_mul,eval_ofNat,eval_X,eval_one] at hx'
    exact h.trans hx'
  have draw : roundDrawBound n ≤ x := by
    have hx' : (drawPolynomial X).eval y ≤ x := by simp only [x,pad,eval_add,eval_X]; omega
    rw [drawPolynomial_eval,eval_X] at hx'
    unfold roundDrawBound EncodedUniformRounding.drawBound at hx' ⊢
    exact (show ((6*(4*n^2))^3+2)*(2*(6*(4*n^2))*(6*(4*n^2))) ≤
      ((6*(4*y^2))^3+2)*(2*(6*(4*y^2))*(6*(4*y^2))) by gcongr).trans hx'
  have source : (PhysicalSourceDispatch.input D).length ≤ x := by
    have hx' : wire.eval y ≤ x := by simp only [x,pad,eval_add,eval_X]; omega
    apply (PhysicalSourceSizeBounds.source_size_le D).trans
    apply le_trans ?_ hx'
    simp only [wire,eval_add,eval_mul,eval_ofNat,eval_X,PhysicalSourceSizeBounds.sourceSizeBound]
    have stored : LambdaRowProgram.rowBits D.costs.toList ≤ y := (Nat.le_add_right _ 1).trans hb
    gcongr
  have positive := ChargedVertexModes.priceWidth_positive D
  have fits := ChargedVertexModes.priceWidth_bounds D
  have eBound : e ≤ x := (Nat.le_succ _).trans he
  have ht : T ≤ z := (trialLimit_le D (roundDrawBound n) e (e+1) (hn.trans hy) (hb.trans hy)
    draw eBound he fits).trans (Nat.le_add_right _ _)
  rw [eval_comp]
  refine hp D (runner mode) (roundDrawBound n) e (e+1) tape (hn.trans hy) (hb.trans hy) draw eBound he source
    positive fits (fun rows stored row member bits r call => ?_) ran
  apply runner_paid q hq mode _ bits (VertexReductionWidths.fractional_input D stored member) ((hn.trans hy).trans hx) ht ?_ call
  have H := eval_mono PhysicalSourceDispatch.instructionPolynomial (source.trans hx)
  have price := (hb.trans hy).trans hx
  exact max_le (by omega) (by omega)

theorem vertex_wire_polynomial : ∃ p : Polynomial ℕ, ∀ (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits)
    {n : ℕ} {r : Result n}, (vertexWithCost κ mode source tape).1=some ⟨n,r⟩ →
      (vertexWithCost κ mode source tape).2+r.dispatch+r.readback+r.roundingAndSelection ≤ p.eval (source.length+κ) :=
  PhysicalWireCostEnvelope.vertex_wire_polynomial_for @vertex vertex_polynomial

end DirectedFlowCutGap.PhysicalAmplifiedBinaryVertex
