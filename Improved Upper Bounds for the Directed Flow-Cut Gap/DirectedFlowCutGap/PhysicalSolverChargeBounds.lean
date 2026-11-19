import DirectedFlowCutGap.PhysicalSolverCharges
import DirectedFlowCutGap.PhysicalSourceSizeBounds

/-!
# Composition of the source-dispatch and readback bounds

The serialization estimate bounds the encoded line graph in the input
dimensions before interpreting it. These bounds cover dispatch and the
serialization, dispatch fuel construction, terminal reads and conversions. The solver completeness theorems give
the separate polynomial bound on the binary sampler's operations.
-/

namespace DirectedFlowCutGap.PhysicalSolverCharges

private theorem eval_mono (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval_add] using Nat.add_le_add hp hq
  | monomial n c =>
    rw [Polynomial.eval_monomial, Polynomial.eval_monomial]
    gcongr

theorem budgets_of_source_length {n l : ℕ} (D : BinaryFractionalGuesses.Input n)
    (h : (PhysicalSourceDispatch.input D).length ≤ l) :
    let bound := PhysicalSourceDispatch.instructionPolynomial.eval l
    dispatchBudget D ≤ PhysicalSourceDispatch.paidPolynomial.eval l ∧
    lookupBudget D ≤ PhysicalSourceReadback.planBound (1 + bound) bound := by
  have hb := eval_mono PhysicalSourceDispatch.instructionPolynomial h
  exact ⟨eval_mono PhysicalSourceDispatch.paidPolynomial h,
    PhysicalSourceReadback.planBound_mono (Nat.add_le_add_left hb 1) hb⟩

theorem vertex_budgets {n : ℕ} (D : BinaryFractionalGuesses.Input n) :
    let size := PhysicalSourceSizeBounds.sourceSizeBound n D.demands.length
      (LambdaRowProgram.rowBits D.costs.toList)
    let bound := PhysicalSourceDispatch.instructionPolynomial.eval size
    dispatchBudget D ≤ PhysicalSourceDispatch.paidPolynomial.eval size ∧
    lookupBudget D ≤ PhysicalSourceReadback.planBound (1 + bound) bound :=
  budgets_of_source_length D (PhysicalSourceSizeBounds.source_size_le D)

theorem edge_budgets {n B : ℕ} (D : EncodedEdgeLineInput.Input n) (hB : 1 ≤ B)
    (hc : ∀ u v : Fin n, (D.costs[u.val][v.val]).num.size ≤ B ∧
      (D.costs[u.val][v.val]).den.size ≤ B) :
    let line := PhysicalEdgeSolver.binaryLineInput D
    let size := PhysicalSourceSizeBounds.lineSourceSizeBound n D.demands.length B
    let bound := PhysicalSourceDispatch.instructionPolynomial.eval size
    dispatchBudget line ≤ PhysicalSourceDispatch.paidPolynomial.eval size ∧
    lookupBudget line ≤ PhysicalSourceReadback.planBound (1 + bound) bound :=
  budgets_of_source_length _ (PhysicalSourceSizeBounds.line_source_size_le D hB hc)

end DirectedFlowCutGap.PhysicalSolverCharges
