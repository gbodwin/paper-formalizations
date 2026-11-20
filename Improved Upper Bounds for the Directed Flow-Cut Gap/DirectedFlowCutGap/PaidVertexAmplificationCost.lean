import DirectedFlowCutGap.PaidVertexAmplification
import DirectedFlowCutGap.PhysicalSolverCostEnvelope

namespace DirectedFlowCutGap.PaidVertexAmplification

open BinaryArithmetic BinaryFractionalRows BinaryRational Polynomial
open EncodedVertexSolver ChargedPhysicalVertexSolver
open PhysicalSolverCostEnvelope (trialEnvelope trialLimit_le rowLimit_le rowEnvelope)

/-- Control words and all reached sample and selection charges are bounded
even when the literal tape ends before the full family is returned. -/
theorem polynomial_on_rows (q : Polynomial ℕ) : ∃ p : Polynomial ℕ,
    ∀ {n B x : ℕ} (D : BinaryFractionalGuesses.Input n) (round : PaidVertexSampling.Runner n)
      (draw extra confidence : ℕ) (plan : PhysicalCoverReader.Plan n) (dispatch readback : ℕ) (tape : Bits),
      n ≤ x → B ≤ x → draw ≤ x → extra ≤ x → confidence ≤ x →
      1 ≤ B → (∀ i, StoredBounded (get D.costs i) B) →
      rowsCount plan ≤ rowLimit (BinaryFractionalGuesses.decodeInput D) →
      (∀ rows, plan=.covers rows → ∀ row ∈ rows, ∀ bits,
        (round (trialLimit (BinaryFractionalGuesses.decodeInput D) draw extra confidence)
          (roundingInput (BinaryFractionalGuesses.decodeInput D) row) bits).2 ≤ q.eval (trialEnvelope.eval x+x)) →
      (runWithPlan D round draw extra confidence plan dispatch readback tape).2 ≤ p.eval x := by
  let sum := X*(C 2048*((X+1)*(X+1)+1)^2+C 4)+1
  let compare := C 2048*(X*(X+1)+C 2)^2
  let row := q.comp (trialEnvelope+X)+sum+C 10+compare+C 4
  let sample := (C 4*X+C 3)*row+C 4*X+C 11
  let select := ((X+1)*sum+X*compare)+(C 20*(X+1)^2+C 5)
  let amplify := (X+1)*(sample+C 4)+1+select
  let controls := BinaryAmplificationPreparation.budget (5*X : Polynomial ℕ)
  refine ⟨controls+amplify,?_⟩
  intro n B x D round draw extra confidence plan dispatch readback tape hn hB hd he hc positive fits planRows each
  let T := trialLimit (BinaryFractionalGuesses.decodeInput D) draw extra confidence
  let R := q.eval (trialEnvelope.eval x+x)
  have rows := rowLimit_le D fits
  have rowsBound : rowsCount plan ≤ 4*x+3 := by
    unfold rowEnvelope at rows
    omega
  have perSample : let setup := BinaryAmplificationPreparation.prepare D.costs draw extra confidence
      ∀ bits, (PaidVertexSampling.fromPlanWith D setup.costs round setup.trials plan bits).2 ≤ sample.eval x := by
    dsimp only
    intro bits
    simp only [BinaryAmplificationPreparation.costs_value,BinaryAmplificationPreparation.trials_value D]
    refine (PaidVertexSampling.fromPlan_paid D _ round T R positive fits plan bits (fun rows h y member bits =>
      each rows h y member bits)).trans ?_
    simp only [sample,row,compare,sum,eval_mul,eval_add,eval_C,eval_X,eval_one,eval_pow,eval_comp,
      ChargedCutSelection.rowBound,BinaryFractionalRows.sumBound,Nat.zero_add,Nat.add_assoc]
    dsimp only [R]
    gcongr
  have raw := runWithPlan_paid D round draw extra confidence plan dispatch readback (sample.eval x)
    positive fits tape perSample
  have prefixBound : BinaryAmplificationPreparation.budget (n+B+draw+extra+confidence) ≤ controls.eval x := by
    simp only [controls,BinaryAmplificationPreparation.budget_eval,eval_mul,eval_ofNat,eval_X]
    exact BinaryAmplificationPreparation.budget_mono (by omega)
  have loop : (extra+1)*(sample.eval x+4)+1+(BinaryCutPriceSelection.selectionBound extra n B+(20*(extra+1)^2+5)) ≤
      amplify.eval x := by
    simp only [amplify,select,compare,sum,eval_mul,eval_add,eval_C,eval_X,eval_one,eval_pow,
      BinaryCutPriceSelection.selectionBound,BinaryFractionalRows.sumBound]
    gcongr
  rw [eval_add]
  exact raw.trans (Nat.add_le_add prefixBound loop)

end DirectedFlowCutGap.PaidVertexAmplification
