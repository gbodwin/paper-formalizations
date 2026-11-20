import DirectedFlowCutGap.PaidFramedVertexCost
import DirectedFlowCutGap.LiteralRoundSchedule

/-! Bound the shared trials and attempted rounds actually selected by the
vertex solver at an accepted original source. -/
namespace DirectedFlowCutGap.FramedVertexTrials

open BinaryArithmetic BinaryFractionalRows BinaryRational Polynomial
open EncodedVertexAmplification PhysicalSolverCostEnvelope
open ChargedPhysicalVertexSolver (rowsCount rowsCount_le)
open PhysicalIntegerRoundingCost (eval_mono)

theorem polynomial : ∃ trials visits : Polynomial ℕ,
    ∀ {n : ℕ} {D : BinaryFractionalGuesses.Input n} {source : Bits},
      (PhysicalSourceInputJoin.vertex source).1=some ⟨n,D⟩ →
      ∀ (κ : ℕ) (mode : ChargedVertexModes.Mode) (tape : Bits),
        let x := source.length+κ
        let cover := PhysicalCoverReader.plan (BinaryFractionalGuesses.solveInput D).1
        let controls := BinarySolverOuterControls.vertex n κ
        let ready := BinaryAmplificationPreparation.prepare D.costs controls.draws controls.extra controls.confidence
        ready.trials ≤ trials.eval x ∧
          (LiteralRoundSchedule.amplified D (PaidVertexRounding.runner mode)
            controls.draws controls.extra controls.confidence cover tape).1.length ≤ visits.eval x := by
  let draw := drawPolynomial (X : Polynomial ℕ)
  let exponent : Polynomial ℕ := (X+2)*X+1
  let pad := X+draw+exponent
  let rows : Polynomial ℕ := 4*X+3
  refine ⟨trialEnvelope.comp pad,exponent*rows,?_⟩
  intro n D source parsed κ mode tape
  let x := source.length+κ
  let y := pad.eval x
  let cover := PhysicalCoverReader.plan (BinaryFractionalGuesses.solveInput D).1
  let controls := BinarySolverOuterControls.vertex n κ
  have original : (ChargedSourceAssembly.vertex source).1=some ⟨n,D⟩ := by
    simpa only [ChargedSourceAssembly.vertex_value,← PhysicalSourceInputJoin.vertex_value] using parsed
  obtain ⟨dimension,_,fields⟩ := ChargedSourceAssembly.vertex_dimensions original
  have size : source.length ≤ x := Nat.le_add_right _ _
  have nBound := dimension.trans size
  have confidence : κ ≤ x := Nat.le_add_left _ _
  have fits (i : Fin n) : StoredBounded (get D.costs i) source.length := by
    apply fields
    change D.costs[i.val] ∈ D.costs.toList
    have inside : i.val < D.costs.toList.length := by simp [i.isLt]
    simpa only [Vector.getElem_toList] using List.getElem_mem inside
  have inPad : x ≤ y := by
    simp only [y,pad,eval_add,eval_X]
    omega
  have extra : controls.extra+1 ≤ exponent.eval x := by
    have bound := Nat.add_le_add_right
      ((exponent_le n κ).trans (Nat.mul_le_mul (Nat.add_le_add_right nBound 2) confidence)) 1
    simpa only [controls,BinarySolverOuterControls.vertex_extra,exponent,eval_add,eval_mul,
      eval_X,eval_ofNat,eval_one] using bound
  have sameConfidence : controls.confidence=controls.extra+1 := by
    simp only [controls,BinarySolverOuterControls.vertex_confidence,BinarySolverOuterControls.vertex_extra]
  have expInPad : exponent.eval x ≤ y := by
    simp only [y,pad,eval_add]
    omega
  have draws : controls.draws ≤ y := by
    have bound : draw.eval x ≤ y := by simp only [y,pad,eval_add]; omega
    apply le_trans _ bound
    change controls.draws ≤ (drawPolynomial (X : Polynomial ℕ)).eval x
    rw [BinarySolverOuterControls.vertex_draws,drawPolynomial_eval,eval_X]
    unfold roundDrawBound EncodedUniformRounding.drawBound
    gcongr
  constructor
  · rw [BinaryAmplificationPreparation.trials_value D,eval_comp]
    exact trialLimit_le D controls.draws controls.extra controls.confidence (nBound.trans inPad)
      (size.trans inPad) draws (((Nat.le_succ _).trans extra).trans expInPad)
      (sameConfidence.symm ▸ extra.trans expInPad) fits
  · have rowBound : rowsCount cover ≤ rows.eval x := by
      have count := (rowsCount_le D).trans (rowLimit_le D fits)
      change rowsCount cover ≤ rowEnvelope n source.length at count
      simp only [rows,eval_add,eval_mul,eval_ofNat,eval_X,rowEnvelope] at count ⊢
      omega
    rw [eval_mul]
    exact (LiteralRoundSchedule.amplified_count D (PaidVertexRounding.runner mode)
      controls.draws controls.extra controls.confidence cover tape).trans (Nat.mul_le_mul extra rowBound)

end DirectedFlowCutGap.FramedVertexTrials
