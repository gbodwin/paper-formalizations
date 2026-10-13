import DirectedFlowCutGap.SourcePackingPolynomialCosts

noncomputable section
namespace DirectedFlowCutGap.SourcePackingPolynomial
open Polynomial ImmutableReferenceSimulation ImmutableReferenceTerminal

/-- One fixed polynomial in original encoded-source length. -/
def instructionPolynomial : Polynomial ℕ :=
  29*X+31+poly_EnumeratedPacking_instructionBound (X+1) (X+1) (X+1)+2

theorem instruction_le_eval (N : ℕ) :
    SourcePacking.sourceBound N ≤ instructionPolynomial.eval N := by
  have h := bound_EnumeratedPacking_instructionBound N
    (n:=N+1) (d:=N+1) (B:=N+1) (p_n:=X+1) (p_d:=X+1) (p_B:=X+1)
    (by simp) (by simp) (by simp)
  simp only [SourcePacking.sourceBound,instructionPolynomial,Polynomial.eval_add,
    Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
  omega

/-- The actual reference simulation and its terminal attempt, as a polynomial. -/
def physicalPolynomial : Polynomial ℕ :=
  C (controlCost 8490+128)*instructionPolynomial*(2+2*instructionPolynomial)^2+
    C (controlCost 8490+128)*(2+instructionPolynomial)*(1+instructionPolynomial)

theorem physical_eval (N : ℕ) : physicalPolynomial.eval N=
    completeBound 8490 1 0 (instructionPolynomial.eval N) := by
  simp only [physicalPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_C,Polynomial.eval_ofNat,Polynomial.eval_one,completeBound,runBound,stepBound]
  ring

theorem physical_le_eval (N : ℕ) :
    completeBound 8490 1 0 (SourcePacking.sourceBound N) ≤ physicalPolynomial.eval N := by
  rw [physical_eval]
  exact SupportSearchEncoding.complete_mono 8490 1 0 _ _ (instruction_le_eval N)

theorem fixed_polynomial_bound : ∃ p : Polynomial ℕ, ∀ N : ℕ,
    completeBound 8490 1 0 (SourcePacking.sourceBound N) ≤ p.eval N :=
  ⟨physicalPolynomial,physical_le_eval⟩
end DirectedFlowCutGap.SourcePackingPolynomial
