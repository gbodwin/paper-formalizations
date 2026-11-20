import DirectedFlowCutGap.PaidFramedEdgeCost

/-! Bound the actual shared trial count using original source length and
the numerical confidence degree. Stored prices contribute to the wire length. -/
namespace DirectedFlowCutGap.FramedEdgeTrials

open BinaryArithmetic Polynomial
open EncodedVertexAmplification PhysicalSolverCostEnvelope
open ChargedPhysicalVertexSolver (trialLimit)
open PhysicalIntegerRoundingCost (eval_mono)

private theorem table_length (fields : List (Bits × Bits)) :
    (SourceRowTableProgram.encode fields).length =
      2*SourceRowTableProgram.bits fields+3*fields.length+1 := by
  induction fields with
  | nil => rfl
  | cons field fields ih =>
    obtain ⟨a,b⟩ := field
    simp only [SourceRowTableProgram.encode,SourceRowTableProgram.bits,List.length_cons,List.length_append,
      SelfDelimitedWordProgram.encode_length,ih]
    omega

private theorem width_le_source {n : ℕ} (D : BinaryFractionalGuesses.Input n) :
    ChargedVertexModes.priceWidth D ≤ (PhysicalSourceDispatch.input D).length := by
  let fields := SourcePacking.capacityFields D.costs
  have size : SourceRowTableProgram.bits fields=LambdaRowProgram.rowBits D.costs.toList :=
    FinalDispatchEnvelope.fields_bits _
  change LambdaRowProgram.rowBits D.costs.toList+1 ≤ (PackingSourceInput.encode fields _ _).length
  simp only [PackingSourceInput.encode,List.length_append,table_length,size]
  omega

theorem polynomial : ∃ p : Polynomial ℕ, ∀ {n : ℕ} {D : EncodedEdgeInput.Input n} {source : Bits},
    (PhysicalSourceInputJoin.edge source).1=some ⟨n,D⟩ → ∀ κ : ℕ,
      let raw := (PhysicalBinaryEdgeWire.decodeWithCost D).1
      let line := (PhysicalAmplifiedBinaryEdge.lineWithCost raw).1
      let controls := BinarySolverOuterControls.edge n κ
      (BinaryAmplificationPreparation.prepare line.costs controls.draws controls.extra controls.confidence).trials ≤
        p.eval (source.length+κ) := by
  obtain ⟨serialized,lengthBound⟩ := PaidDirectEdgeWire.serialized_line_length
  let vertices := BinaryEdgeGadget.dimension (X : Polynomial ℕ)
  let exponent : Polynomial ℕ := (X+2)*X+1
  let pad := serialized+drawPolynomial vertices+exponent
  refine ⟨trialEnvelope.comp pad,?_⟩
  intro n D source found κ
  let x := source.length+κ
  let y := pad.eval x
  let raw := (PhysicalBinaryEdgeWire.decodeWithCost D).1
  let line := (PhysicalAmplifiedBinaryEdge.lineWithCost raw).1
  let controls := BinarySolverOuterControls.edge n κ
  have saved : (ChargedSourceAssembly.edge source).1=some ⟨n,D⟩ :=
    (ChargedSourceAssembly.edge_value source).trans ((PhysicalSourceInputJoin.edge_value source).symm.trans found)
  have nBound : n ≤ x := (ChargedSourceAssembly.edge_dimensions saved).1.trans (Nat.le_add_right _ _)
  have confidence : κ ≤ x := Nat.le_add_left _ _
  have lineLength : (PhysicalSourceDispatch.input line).length ≤ serialized.eval x := by
    rw [← BinarySourceSerialization.run_value]
    exact (lengthBound found).trans (eval_mono _ (Nat.le_add_right _ _))
  have input : (PhysicalSourceDispatch.input line).length ≤ y := by
    apply lineLength.trans
    simp only [y,pad,eval_add]
    omega
  have lineDim := ((Nat.le_succ _).trans (BinarySourceSerialization.input_dimensions line)).trans input
  have prices := (width_le_source line).trans input
  have extra : controls.extra+1 ≤ y := by
    have h := Nat.add_le_add_right ((exponent_le n κ).trans (Nat.mul_le_mul (Nat.add_le_add_right nBound 2) confidence)) 1
    rw [BinarySolverOuterControls.edge_extra]
    apply h.trans
    simp only [y,pad,exponent,eval_add,eval_mul,eval_ofNat,eval_X,eval_one]
    omega
  have dim : BinaryEdgeGadget.dimension n ≤ vertices.eval x := by
    simp only [vertices,BinaryEdgeGadget.dimension,eval_add,eval_mul,eval_X,eval_ofNat]
    gcongr
  have draws : controls.draws ≤ y := by
    have upper : (drawPolynomial vertices).eval x ≤ y := by
      simp only [y,pad,eval_add]
      omega
    apply le_trans _ upper
    rw [BinarySolverOuterControls.edge_draws,drawPolynomial_eval]
    have width : 2*n*(Nat.log2 n+4) ≤ vertices.eval x :=
      (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.log2_le_self _) 4)).trans dim
    unfold EncodedEdgeSolver.drawBound roundDrawBound EncodedUniformRounding.drawBound
    gcongr
  change (BinaryAmplificationPreparation.prepare line.costs controls.draws controls.extra controls.confidence).trials ≤
    (trialEnvelope.comp pad).eval x
  rw [BinaryAmplificationPreparation.trials_value line,eval_comp]
  have sameConfidence : controls.confidence=controls.extra+1 := by
    simp only [controls,BinarySolverOuterControls.edge_confidence,BinarySolverOuterControls.edge_extra]
  exact trialLimit_le line controls.draws controls.extra controls.confidence lineDim prices draws
    ((Nat.le_succ _).trans extra) (sameConfidence.symm ▸ extra) (ChargedVertexModes.priceWidth_bounds line)

end DirectedFlowCutGap.FramedEdgeTrials
