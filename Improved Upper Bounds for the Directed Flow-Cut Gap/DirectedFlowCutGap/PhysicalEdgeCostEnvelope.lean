import DirectedFlowCutGap.PhysicalSolverCostEnvelope

/-! Bound the recorded phases of the amplified edge execution in the original
edge dimensions. The dyadic gadget supplies the rounding dimension. -/

namespace DirectedFlowCutGap.PhysicalEdgeCostEnvelope

open BinaryArithmetic BinaryFractionalRows BinaryRational Polynomial
open EncodedVertexAmplification EncodedEdgeLineInput
open PhysicalSolverCostEnvelope

set_option maxHeartbeats 1000000 in
private theorem round_paid (q : Polynomial ℕ)
    (bound : ∀ n T x, n ≤ x → T ≤ x →
      (∀ (D : EncodedUnitCostReplication.Input n) tape r, PhysicalVertexRounding.weighted T D tape = some r → r.paid ≤ q.eval x) ∧
      (∀ (D : EncodedUnitCostReplication.Input n) tape r, PhysicalVertexRounding.size T D tape = some r → r.paid ≤ q.eval x))
    {n T x : ℕ} (D : Input n) (mode : ChargedVertexModes.Mode)
    (dimensions : 2*n*(Nat.log2 n+4) ≤ x) (trials : T ≤ x)
    (input : EncodedVertexSolver.RoundingInput (lineSize n)) (tape : Bits)
    (r : PhysicalIntegerRounding.Result (lineSize n)) (run : PhysicalAmplifiedEdgeSolver.round D mode T input tape = some r) :
    r.paid ≤ q.eval x := by
  let gadget := EncodedEdgeGadget.build (roundingInput D input.weights)
  let selected := PhysicalAmplifiedEdgeSolver.rounding (n:=gadget.size) mode
  change ((selected T gadget.data tape).map
    (PhysicalVertexRounding.project (fun mask => (toLine (EncodedEdgeRounding.pullback gadget mask),0)) 0))=some r at run
  cases ran : selected T gadget.data tape with
  | none => simp [ran] at run
  | some out =>
    simp only [ran,Option.map_some,Option.some.injEq] at run
    have size := (EncodedEdgeGadget.build_size_le (roundingInput D input.weights)).trans dimensions
    rw [← run]
    change 0+out.paid+0 ≤ q.eval x
    simp only [Nat.zero_add,Nat.add_zero]
    cases mode
    · exact (bound gadget.size T x size trials).1 gadget.data tape out ran
    · exact (bound gadget.size T x size trials).2 gadget.data tape out ran

set_option maxHeartbeats 1400000 in
/-- Polynomial in the original vertex count, demand count, cost field width and
the confidence exponent. This covers the counters returned by the edge runner. -/
theorem edge_polynomial : ∃ p : Polynomial ℕ, ∀ {n B : ℕ} (κ : ℕ) (D : Input n)
    (mode : ChargedVertexModes.Mode) (tape : Bits), 1 ≤ B →
    (∀ u v : Fin n, (D.costs[u.val][v.val]).num.size ≤ B ∧ (D.costs[u.val][v.val]).den.size ≤ B) →
    ∀ {out : PhysicalAmplifiedEdgeSolver.EdgeResult n},
      PhysicalAmplifiedEdgeSolver.run κ D mode tape = some out →
        out.dispatch+out.readback+out.roundingAndSelection ≤ p.eval (n+D.demands.length+B+κ) := by
  obtain ⟨q,hq⟩ := PhysicalVertexRoundingCost.polynomial_bound
  obtain ⟨p,hp⟩ := run_polynomial q
  let line : Polynomial ℕ := X*C 2+X*X
  let costs := line+X+line*(C 2*X)+1
  let wire := C 2*(costs+line*line+X*(line+line))+C 3*(line+line+X)+C 3
  let vertices : Polynomial ℕ := C 2*X*(X+C 4)
  let exponent : Polynomial ℕ := (X+C 2)*X+1
  let pad := line+(costs+1)+wire+vertices+exponent+drawPolynomial vertices
  refine ⟨p.comp pad,?_⟩
  intro n B κ D mode tape positive fits out actual
  let y := n+D.demands.length+B+κ
  let x := pad.eval y
  let binary := PhysicalEdgeSolver.binaryLineInput D
  let W := ChargedVertexModes.priceWidth binary
  let e := confidenceExponent n κ
  let draw := EncodedEdgeSolver.drawBound n
  let T := ChargedPhysicalVertexSolver.trialLimit (BinaryFractionalGuesses.decodeInput binary) draw e (e+1)
  have hn : n ≤ y := by dsimp only [y]; omega
  have hd : D.demands.length ≤ y := by dsimp only [y]; omega
  have hb : B ≤ y := by dsimp only [y]; omega
  have hk : κ ≤ y := by dsimp only [y]; omega
  have hline : lineSize n ≤ line.eval y := by
    simp only [line,eval_add,eval_mul,eval_C,eval_X,lineSize]
    gcongr
  have hs : PhysicalEdgeSolver.lineInputSizeBound n D.demands.length B ≤ costs.eval y := by
    simp only [costs,eval_add,eval_mul,eval_C,eval_X,eval_one,PhysicalEdgeSolver.lineInputSizeBound]
    gcongr
  have hl : lineSize n ≤ x := by
    apply hline.trans
    simp only [x,pad,eval_add]
    omega
  have hW : W ≤ x := by
    have store := PhysicalEdgeSolver.line_size_le D positive fits
    change OriginalStoreInitial.inputSize binary.costs binary.demands ≤ _ at store
    unfold OriginalStoreInitial.inputSize at store
    have lim := store.trans hs
    simp only [x,pad,eval_add,eval_one,W,ChargedVertexModes.priceWidth]
    omega
  have he : e+1 ≤ x := by
    have h := Nat.add_le_add_right ((exponent_le n κ).trans (Nat.mul_le_mul (Nat.add_le_add_right hn 2) hk)) 1
    have next : exponent.eval y ≤ x := by simp only [x,pad,eval_add]; omega
    simp only [exponent,eval_add,eval_mul,eval_C,eval_X,eval_one] at next
    exact h.trans next
  have dim : 2*n*(Nat.log2 n+4) ≤ vertices.eval y := by
    have hnLog : Nat.log2 n ≤ y := (Nat.log2_le_self n).trans hn
    simp only [vertices,eval_add,eval_mul,eval_C,eval_X]
    gcongr
  have draws : draw ≤ x := by
    have b : (drawPolynomial vertices).eval y ≤ x := by simp only [x,pad,eval_add]; omega
    rw [drawPolynomial_eval] at b
    apply le_trans ?_ b
    unfold draw EncodedEdgeSolver.drawBound roundDrawBound EncodedUniformRounding.drawBound
    gcongr
  have source : (PhysicalSourceDispatch.input binary).length ≤ x := by
    have h : wire.eval y ≤ x := by simp only [x,pad,eval_add]; omega
    apply (PhysicalSourceSizeBounds.line_source_size_le D positive fits).trans
    apply le_trans ?_ h
    simp only [PhysicalSourceSizeBounds.lineSourceSizeBound,PhysicalSourceSizeBounds.sourceSizeBound,
      wire,eval_add,eval_mul,eval_C,eval_X]
    gcongr
  have eBound : e ≤ x := (Nat.le_add_right e 1).trans he
  have good := ChargedVertexModes.priceWidth_bounds binary
  have trials : T ≤ trialEnvelope.eval x+x :=
    (trialLimit_le binary draw e (e+1) hl hW draws eBound he good).trans (Nat.le_add_right _ _)
  have vsize : 2*n*(Nat.log2 n+4) ≤ trialEnvelope.eval x+x := by
    apply dim.trans
    simp only [x,pad,eval_add]
    omega
  change ((PhysicalAmplifiedVertexSolver.run binary (PhysicalAmplifiedEdgeSolver.round D mode) draw e (e+1) tape).map
    fun r => ⟨EncodedEdgeSolver.outputFor D r.output,r.suffix,r.dispatch,r.readback,r.roundingAndSelection⟩)=some out at actual
  cases hv : PhysicalAmplifiedVertexSolver.run binary (PhysicalAmplifiedEdgeSolver.round D mode) draw e (e+1) tape with
  | none => simp [hv] at actual
  | some r =>
    simp only [hv,Option.map_some,Option.some.injEq] at actual
    rw [← actual,eval_comp]
    exact hp binary (PhysicalAmplifiedEdgeSolver.round D mode) draw e (e+1) tape hl hW draws eBound he source
      (ChargedVertexModes.priceWidth_positive binary) good (round_paid q hq D mode vsize trials) hv

end DirectedFlowCutGap.PhysicalEdgeCostEnvelope
