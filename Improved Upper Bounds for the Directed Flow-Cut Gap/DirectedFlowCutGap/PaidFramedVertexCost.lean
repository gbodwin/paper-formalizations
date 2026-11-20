import DirectedFlowCutGap.PaidFramedVertexWire
import DirectedFlowCutGap.PaidVertexRoundingCost
import DirectedFlowCutGap.PaidVertexAmplificationCost
namespace DirectedFlowCutGap.PaidFramedVertexWire

open BinaryArithmetic BinaryRational Polynomial
open PhysicalSolverCostEnvelope EncodedVertexAmplification
open ChargedPhysicalVertexSolver (trialLimit)
open PhysicalIntegerRoundingCost (eval_mono)
open PhysicalCoverAccess (Read)

attribute [local irreducible] run PhysicalSourceInputJoin.vertex

set_option maxHeartbeats 1600000 in
theorem run_polynomial : ∃ p : Polynomial ℕ, ∀ {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode)
    (D : BinaryFractionalGuesses.Input n) (tape : Bits), (run κ mode D tape).2 ≤ p.eval (vertexSize D κ) := by
  obtain ⟨q,hq⟩ := PaidVertexRounding.polynomial_bound
  obtain ⟨p,hp⟩ := PaidVertexAmplification.polynomial_on_rows q
  let wire : Polynomial ℕ := 2*(X+X*X+X*(X+X))+3*(X+X+X)+3
  let exponent : Polynomial ℕ := (X+2)*X+1
  let pad := X+wire+exponent+drawPolynomial X
  let inst := PhysicalSourceDispatch.instructionPolynomial
  let lookup := PhysicalSourceReadback.planBound (1+inst) inst
  let phases := PhysicalSourceDispatch.paidPolynomial+lookup+p
  refine ⟨phases.comp pad+BinarySolverOuterControls.budget X X,?_⟩
  intro n κ mode D tape
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
  have confidence : κ ≤ y := by dsimp only [y,vertexSize]; omega
  have he : e+1 ≤ x := by
    have h := Nat.add_le_add_right ((exponent_le n κ).trans (Nat.mul_le_mul (Nat.add_le_add_right hn 2) confidence)) 1
    have next : exponent.eval y ≤ x := by simp only [x,pad,eval_add,eval_X]; omega
    simp only [exponent,eval_add,eval_mul,eval_ofNat,eval_X,eval_one] at next
    exact h.trans next
  have draw : roundDrawBound n ≤ x := by
    have bound : (drawPolynomial X).eval y ≤ x := by simp only [x,pad,eval_add,eval_X]; omega
    rw [drawPolynomial_eval,eval_X] at bound
    unfold roundDrawBound EncodedUniformRounding.drawBound at bound ⊢
    exact (show ((6*(4*n^2))^3+2)*(2*(6*(4*n^2))*(6*(4*n^2))) ≤
      ((6*(4*y^2))^3+2)*(2*(6*(4*y^2))*(6*(4*y^2))) by gcongr).trans bound
  have source : (PhysicalSourceDispatch.input D).length ≤ x := by
    have bound : wire.eval y ≤ x := by simp only [x,pad,eval_add,eval_X]; omega
    apply (PhysicalSourceSizeBounds.source_size_le D).trans
    apply le_trans ?_ bound
    simp only [wire,eval_add,eval_mul,eval_ofNat,eval_X,PhysicalSourceSizeBounds.sourceSizeBound]
    have stored : LambdaRowProgram.rowBits D.costs.toList ≤ y := (Nat.le_add_right _ 1).trans hb
    gcongr
  have positive := ChargedVertexModes.priceWidth_positive D
  have fits := ChargedVertexModes.priceWidth_bounds D
  have eBound : e ≤ x := (Nat.le_succ _).trans he
  have ht : T ≤ z := (trialLimit_le D (roundDrawBound n) e (e+1) (hn.trans hy) (hb.trans hy)
    draw eBound he fits).trans (Nat.le_add_right _ _)
  obtain ⟨dispatch,reader,hdx,hrx,observed⟩ := run_paid κ mode D tape
  let plan := PhysicalCoverReader.plan (BinaryFractionalGuesses.solveInput D).1
  have work := hp D (PaidVertexRounding.runner mode) (roundDrawBound n) e (e+1) plan dispatch reader tape
    (hn.trans hy) (hb.trans hy) draw eBound he positive fits (ChargedPhysicalVertexSolver.rowsCount_le D)
    (fun rows stored row member bits => by
      apply hq ((hn.trans hy).trans hx) ht _ mode _ (VertexReductionWidths.fractional_input D stored member) bits
      have H := eval_mono PhysicalSourceDispatch.instructionPolynomial (source.trans hx)
      have price := (hb.trans hy).trans hx
      exact max_le (by omega) (by omega))
  have dispatchWork := hdx.trans (eval_mono PhysicalSourceDispatch.paidPolynomial source)
  have readerWork : reader ≤ lookup.eval x := by
    apply hrx.trans
    simp only [lookup,PhysicalSourceReadback.planBound_eval,eval_add,eval_one]
    exact PhysicalSourceReadback.planBound_mono (Nat.add_le_add_left (eval_mono _ source) 1) (eval_mono _ source)
  have meter := (BinarySolverOuterControls.vertex_paid n κ).trans (BinarySolverOuterControls.budget_mono hn confidence)
  rw [BinarySolverOuterControls.vertex_draws,BinarySolverOuterControls.vertex_extra,BinarySolverOuterControls.vertex_confidence] at observed
  rw [observed]
  simp only [eval_add,eval_comp,BinarySolverOuterControls.budget_eval,eval_X,phases]
  change (BinarySolverOuterControls.vertex n κ).paid+dispatch+reader+
    (PaidVertexAmplification.runWithPlan D (PaidVertexRounding.runner mode) (roundDrawBound n) e (e+1)
      plan dispatch reader tape).2 ≤ PhysicalSourceDispatch.paidPolynomial.eval x+lookup.eval x+p.eval x+
        BinarySolverOuterControls.budget y y
  exact (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add meter dispatchWork) readerWork) work).trans_eq (by ac_rfl)

private theorem rowBits_le {x : ℕ} (qs : List Fraction) (fits : ∀ q ∈ qs, StoredBounded q x) :
    LambdaRowProgram.rowBits qs ≤ qs.length*(x+x) := by
  induction qs with
  | nil => simp [LambdaRowProgram.rowBits]
  | cons q qs ih =>
      obtain ⟨a,b⟩ := fits q List.mem_cons_self
      have more := ih (fun r hr => fits r (List.mem_cons_of_mem _ hr))
      simp only [LambdaRowProgram.rowBits,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega

set_option maxHeartbeats 1200000 in
theorem wire_polynomial : ∃ p : Polynomial ℕ, ∀ (κ : ℕ) (mode : ChargedVertexModes.Mode) (source tape : Bits),
    (vertexWithCost κ mode source tape).2 ≤ p.eval (source.length+κ) := by
  obtain ⟨p,hp⟩ := run_polynomial
  let pad : Polynomial ℕ := X+X+1+C 2*X^2+X
  refine ⟨PhysicalSourceInputJoin.parsePolynomial+p.comp pad,?_⟩
  intro κ mode source tape
  let x := source.length+κ
  have hS : source.length ≤ x := Nat.le_add_right _ _
  have confidence : κ ≤ x := Nat.le_add_left _ _
  have parse := ((PhysicalSourceInputJoin.vertex_paid source).trans_eq
    (PhysicalSourceInputJoin.parsePolynomial_eval _).symm).trans (eval_mono _ hS)
  rw [eval_add,eval_comp]
  unfold vertexWithCost
  apply Read.bind_bound parse
  rintro ⟨n,D⟩ stored
  have found : (ChargedSourceAssembly.vertex source).1=some ⟨n,D⟩ := by
    rwa [ChargedSourceAssembly.vertex_value,← PhysicalSourceInputJoin.vertex_value]
  obtain ⟨size,demands,fields⟩ := ChargedSourceAssembly.vertex_dimensions found
  have width := rowBits_le D.costs.toList fields
  rw [Vector.length_toList] at width
  have padded : vertexSize D κ ≤ pad.eval x := by
    simp only [pad,eval_add,eval_mul,eval_pow,eval_C,eval_X,eval_one,vertexSize,ChargedVertexModes.priceWidth]
    have hn := size.trans hS
    have w := width.trans (show n*(source.length+source.length) ≤ x*(x+x) by gcongr)
    nlinarith [size.trans hS,demands.trans hS]
  exact (hp κ mode D tape).trans (eval_mono p padded)

end DirectedFlowCutGap.PaidFramedVertexWire
