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

set_option maxHeartbeats 1500000 in
/-- Bound all reached row selection, including a sample whose later row fails. -/
theorem row_work_overhead (raw phase : Polynomial ℕ) : ∃ p : Polynomial ℕ,
    ∀ {n B x : ℕ} (D : BinaryFractionalGuesses.Input n) (round : PaidVertexSampling.Runner n)
      (draw extra confidence : ℕ) (plan : PhysicalCoverReader.Plan n) (dispatch readback : ℕ) (tape : Bits),
      n ≤ x → B ≤ x → extra ≤ x → 1 ≤ B → (∀ i, StoredBounded (get D.costs i) B) →
      rowsCount plan ≤ rowLimit (BinaryFractionalGuesses.decodeInput D) →
      (∀ rows, plan=.covers rows → ∀ row ∈ rows, ∀ bits,
        (round (trialLimit (BinaryFractionalGuesses.decodeInput D) draw extra confidence)
          (roundingInput (BinaryFractionalGuesses.decodeInput D) row) bits).2 ≤ raw.eval (trialEnvelope.eval x+x)) →
      (∀ rows, plan=.covers rows → ∀ row ∈ rows, ∀ bits out,
        (round (trialLimit (BinaryFractionalGuesses.decodeInput D) draw extra confidence)
          (roundingInput (BinaryFractionalGuesses.decodeInput D) row) bits).1=some out →
          out.paid≤phase.eval (trialEnvelope.eval x+x)) →
      (runWithPlanRowWork D round draw extra confidence plan dispatch readback tape).2 ≤
        (runWithPlanStreamWork D round draw extra confidence plan dispatch readback tape).2+p.eval x := by
  let rows : Polynomial ℕ := 4*X+3
  let sum := X*(C 2048*((X+1)*(X+1)+1)^2+C 4)+1
  let compare := C 2048*(X*(X+1)+C 2)^2
  let row := (raw+phase).comp (trialEnvelope+X)+sum+C 10+compare+C 4
  let sample := rows*row+4*X+11
  let visit := PaidVertexSampling.planWorkBudget X rows sample
  refine ⟨(X+1)*visit,?_⟩
  intro n B x D round draw extra confidence plan dispatch readback tape hn hB he positive fits planRows each returned
  let T := trialLimit (BinaryFractionalGuesses.decodeInput D) draw extra confidence
  let z := trialEnvelope.eval x+x
  let reached := raw.eval z+phase.eval z
  have rowsBound : rowsCount plan ≤ rows.eval x := by
    have bound := rowLimit_le D fits
    unfold rowEnvelope at bound
    simp only [rows,eval_add,eval_mul,eval_ofNat,eval_X]
    omega
  have boundLoop (budget : ℕ) (h : budget ≤ reached) :
      rowsCount plan*(budget+ChargedCutSelection.rowBound n B 0+4)+4*n+11 ≤ sample.eval x := by
    have selection : ChargedCutSelection.rowBound n B 0 ≤ (sum+C 10+compare).eval x := by
      simp only [sum,compare,eval_add,eval_mul,eval_X,eval_C,eval_one,eval_pow,
        ChargedCutSelection.rowBound,BinaryFractionalRows.sumBound,Nat.zero_add]
      gcongr
    have eachRow : budget+ChargedCutSelection.rowBound n B 0+4 ≤ row.eval x := by
      have bound := Nat.add_le_add_right (Nat.add_le_add h selection) 4
      simpa only [reached,row,z,eval_add,eval_comp,eval_C,eval_X,Nat.add_assoc] using bound
    simp only [sample,eval_add,eval_mul,eval_ofNat,eval_X]
    gcongr
  have rawBound := boundLoop (raw.eval z) (Nat.le_add_right _ _)
  have phaseBound : sampleBudget n B (rowsCount plan) (phase.eval z) ≤ sample.eval x := by
    apply le_trans _ (boundLoop (phase.eval z) (Nat.le_add_left _ _))
    have selection : ChargedCutSelection.rowBound n B (phase.eval z) ≤ phase.eval z+ChargedCutSelection.rowBound n B 0+4 := by
      simp only [ChargedCutSelection.rowBound,Nat.zero_add]
      omega
    have total := Nat.mul_le_mul_left (rowsCount plan) selection
    unfold sampleBudget
    omega
  have localPaid : ∀ bits, (PaidVertexSampling.fromPlanWithSelectionWork D (decodeRow D.costs) round T plan bits).2 ≤
      visit.eval x := by
    intro bits
    have paid := PaidVertexSampling.fromPlan_paid D (decodeRow D.costs) round T (raw.eval z) positive fits plan bits each
    have width := (BinaryNaturalOperations.size_le_self _).trans (paid.trans rawBound)
    have known : ∀ v ∈ (PaidVertexSampling.fromPlanWith D (decodeRow D.costs) round T plan bits).1,
        v.1.2.size ≤ sample.eval x := by
      intro v found
      rw [PaidVertexSampling.fromPlan_value] at found
      have budget := PhysicalAmplifiedVertexCost.fromPlan_paid_on_rows D (fun t input tape => (round t input tape).1)
        T (phase.eval z) positive fits plan bits returned (Option.mem_def.mp found)
      exact (BinaryNaturalOperations.size_le_self _).trans (budget.trans phaseBound)
    apply (PaidVertexSampling.fromPlanWithSelectionWork_paid D _ round T plan bits width known).trans
    simp only [visit,PaidVertexSampling.planWorkBudget_eval,eval_X]
    exact PaidVertexSampling.planWorkBudget_mono hn rowsBound le_rfl
  have paid := runWithPlanRowWork_paid D round draw extra confidence plan dispatch readback (visit.eval x) tape
    (by simpa only [BinaryAmplificationPreparation.costs_value,BinaryAmplificationPreparation.trials_value D] using localPaid)
  apply paid.trans
  simp only [eval_mul,eval_add,eval_X,eval_one]
  gcongr

end DirectedFlowCutGap.PaidVertexAmplification
