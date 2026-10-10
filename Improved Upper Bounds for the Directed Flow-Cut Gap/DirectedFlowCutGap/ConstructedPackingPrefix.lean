import DirectedFlowCutGap.EncodedPackingBitBudget
import DirectedFlowCutGap.HeavyPackingPolynomialLaw

/-! The actual binary budget constructor supplies a sufficient prefix for
the same full adaptive packing body. The random input prefix law is still
specified here; generating/encoding it and full storage compilation remain
separate costs. -/
namespace DirectedFlowCutGap.ConstructedPackingPrefix
noncomputable section
open BinaryArithmetic BinaryFractionalRows HeavyCutProvider

theorem budget_value (resources width stored : Bits) :
    value (EncodedPackingBitBudget.run resources width stored).1 =
      HeavyPackingBitBudget.polynomial (value resources) (value width) (value stored) := by
  exact EncodedPackingBitBudget.run_value resources width stored

theorem output_law {n S : ℕ} (adjacency : RetainedGridState.PairFlags n)
    (w : Row n) (B : ℕ) (hw : ∀ i, BinaryRational.StoredBounded (get w i) S)
    (resources width stored : Bits) (hn : value resources = n)
    (hB : value width = B) (hS : value stored = S) :
    (FiniteBinaryPrefix.prefixLaw
      (value (EncodedPackingBitBudget.run resources width stored).1)).map
        (fun xs => ((HeavyPackingPrefix.read adjacency w B resources width).run xs).1) =
      HeavyPackingEntry.run adjacency w B resources width := by
  rw [budget_value,hn,hB,hS]
  exact HeavyPackingPolynomialLaw.output_law adjacency w B hw resources width hn hB

/-- The sufficient length is computed with charged binary arithmetic whose
constant depends only on the fixed expression, before all input words. -/
theorem sufficient_and_charged {n S : ℕ} (adjacency : RetainedGridState.PairFlags n)
    (w : Row n) (B : ℕ) (hw : ∀ i, BinaryRational.StoredBounded (get w i) S)
    (resources width stored : Bits) (hn : value resources = n)
    (hB : value width = B) (hS : value stored = S) (L : ℕ)
    (hr : resources.length ≤ L) (hb : width.length ≤ L) (hs : stored.length ≤ L) :
    FiniteDrawTrees.Within (value (EncodedPackingBitBudget.run resources width stored).1)
      (HeavyPackingPrefix.tree adjacency w B resources width) ∧
    (EncodedPackingBitBudget.run resources width stored).1.length ≤
      BinaryBudgetExpression.widthCoefficient EncodedPackingBitBudget.body*(L+1) ∧
    (EncodedPackingBitBudget.run resources width stored).2 ≤
      BinaryBudgetExpression.costCoefficient EncodedPackingBitBudget.body*(L+1)^2 := by
  refine ⟨?_,EncodedPackingBitBudget.run_bounds resources width stored L hr hb hs⟩
  rw [budget_value,hn,hB,hS]
  exact HeavyPackingBitBudget.within_polynomial adjacency w B hw resources width hn hB

end
end DirectedFlowCutGap.ConstructedPackingPrefix
