import DirectedFlowCutGap.PaidVertexRounding
namespace DirectedFlowCutGap.PaidVertexRounding

open BinaryArithmetic Polynomial EncodedUnitCostReplication
open VertexReductionWidths (InputFits)
open IntegralNetworkFlow.Tabulated
open PhysicalAmplifiedBinaryVertex (arithmeticPolynomial arithmeticPolynomial_eval)

set_option maxHeartbeats 1000000 in
theorem polynomial_bound : ∃ q : Polynomial ℕ, ∀ {n b T y : ℕ},
    n ≤ y → T ≤ y → b ≤ y+1+PhysicalSourceDispatch.instructionPolynomial.eval y →
    ∀ (mode : ChargedVertexModes.Mode) (D : Input n), InputFits D b → ∀ tape,
      (runner mode T D tape).2 ≤ q.eval y := by
  obtain ⟨p,inside⟩ := GuardedCutoffWork.budget_polynomial
  let a : Polynomial ℕ := C 3*X
  let search := a*(a*(a*(C 24+C 17)+C 18+C 4)+C 5)+C 17*a+C 21
  let m : Polynomial ℕ := C 4*X^2
  let uniform := C 3000*m^2+C 1142*m+C 121+p.comp (C 6*m+X)
  let weighted := C 9*X^2*(search+C 224)+C 640*X^4+C 108*X^3+C 316*X^2+C 1011*X+C 206+uniform
  let q := C 60*X^2+C 188*X+C 97+weighted
  refine ⟨q+arithmeticPolynomial,?_⟩
  intro n b T y hn ht fits mode D store tape
  have eval : q.eval y=PhysicalVertexRoundingCost.sizeBudget p y y := by
    simp only [q,weighted,uniform,search,a,m,eval_add,eval_mul,eval_pow,eval_C,eval_X,eval_comp,
      PhysicalVertexRoundingCost.sizeBudget,PhysicalVertexRoundingCost.weightedBudget,
      PhysicalVertexRoundingCost.uniformBudget,CountedSearch.searchBound,CountedSearch.visitBound]
  rw [eval_add,eval,arithmeticPolynomial_eval]
  have graph : PhysicalVertexRoundingCost.sizeBudget p n T ≤ PhysicalVertexRoundingCost.sizeBudget p y y := by
    have inner := PhysicalIntegerRoundingCost.eval_mono p (show 6*(4*n^2)+T ≤ 6*(4*y^2)+y by gcongr)
    unfold PhysicalVertexRoundingCost.sizeBudget PhysicalVertexRoundingCost.weightedBudget
      PhysicalVertexRoundingCost.uniformBudget CountedSearch.searchBound CountedSearch.visitBound
    gcongr
  have math := PhysicalBinaryVertexRounding.sizeBudget_mono hn fits
  cases mode with
  | mass =>
      change (PaidVertexRounding.weighted T D tape).2 ≤ _
      have a : PhysicalVertexRoundingCost.weightedBudget p n T ≤ PhysicalVertexRoundingCost.sizeBudget p n T :=
        Nat.le_add_left _ _
      have b : PhysicalBinaryVertexRounding.weightedBudget n b ≤ PhysicalBinaryVertexRounding.sizeBudget n b :=
        (PhysicalBinaryVertexRounding.weightedBudget_mono (Nat.le_refl _) (Nat.le_succ _)).trans (Nat.le_add_left _ _)
      exact (PaidVertexRounding.weighted_paid p inside T D store tape).trans
        (Nat.add_le_add (a.trans graph) (b.trans math))
  | size =>
      change (size T D tape).2 ≤ _
      exact (size_paid p inside T D store tape).trans (Nat.add_le_add graph math)

end DirectedFlowCutGap.PaidVertexRounding
