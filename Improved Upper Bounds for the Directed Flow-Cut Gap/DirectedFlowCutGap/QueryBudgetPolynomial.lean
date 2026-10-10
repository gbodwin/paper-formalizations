import DirectedFlowCutGap.HeavyQueryBitBudget
import DirectedFlowCutGap.QueryBudgetArithmetic

/-! A deliberately coarse explicit polynomial bounds every adaptive heavy
query's finite fair-bit prefix uniformly in the current cost row. This bounds
bit consumption, not construction of the budget or physical runtime. -/
namespace DirectedFlowCutGap.QueryBudgetPolynomial
open BinaryArithmetic

theorem entry_le {N L : ℕ} (hL : L ≤ N) :
    BinaryEntryTrees.budget N (StatefulBoundedRoundingQuality.canonicalFuel N) L.bits  ≤ 
      QueryBudgetArithmetic.polynomial N := by
  unfold BinaryEntryTrees.budget BinaryControllerTrees.callBudget BinaryTapeBudget.budget
  rw [EncodedEpochParameters.compute_fuel,StatefulBoundedRoundingQuality.canonicalFuel_value,
    value_bits]
  simpa only [QueryBudgetArithmetic.epochs,QueryBudgetArithmetic.width,
    IntegerEpochParameters.fuel,IntegerEpochParameters.restart,FairBitConfidence.trials,
    AllRegimeBoundedTapeLaw.drawBudget,FairBitWords.width,Nat.add_assoc,mul_assoc]
    using QueryBudgetArithmetic.budget_le hL

theorem uniform_bound (n extra : ℕ) :
    HeavyQueryBitBudget.bound n extra  ≤ 
      (extra+1)*QueryBudgetArithmetic.polynomial (24*n^2) := by
  unfold HeavyQueryBitBudget.bound
  apply Finset.sup_le
  intro N hN
  apply Finset.sup_le
  intro L hL
  exact Nat.mul_le_mul_left (extra+1) ((entry_le (by
    have := Finset.mem_range.mp hL;omega)).trans
    (QueryBudgetArithmetic.polynomial_mono (by
      have := Finset.mem_range.mp hN;omega)))

theorem provider_within {n : ℕ} (adjacency : RetainedGridState.PairFlags n)
    (w c : BinaryFractionalRows.Row n) (extra : ℕ) (state : BinarySamplerMetadata.Ledger) :
    FiniteDrawTrees.Within ((extra+1)*QueryBudgetArithmetic.polynomial (24*n^2))
      (BinaryHeavyProviderTrees.draw adjacency w extra state c) :=
  FiniteDrawTrees.within_mono (HeavyQueryBitBudget.provider_within adjacency w c extra state)
    (uniform_bound n extra)

end DirectedFlowCutGap.QueryBudgetPolynomial
