import DirectedFlowCutGap.HeavyPackingBitBudget

/-! The explicit polynomial fair-bit prefix realizes the same complete
adaptive packing result and the original-weight marginal guarantee.
Input/fuel/budget construction and physical execution cost remain separate. -/
namespace DirectedFlowCutGap.HeavyPackingPolynomialLaw
noncomputable section
open BinaryArithmetic BinaryFractionalRows HeavyCutProvider

theorem output_law {n S : ℕ} (adjacency : RetainedGridState.PairFlags n)
    (w : Row n) (B : ℕ) (hw : ∀ i, BinaryRational.StoredBounded (get w i) S)
    (resources width : Bits) (hn : value resources = n) (hB : value width = B) :
    (FiniteBinaryPrefix.prefixLaw (HeavyPackingBitBudget.polynomial n B S)).map
      (fun xs => ((HeavyPackingPrefix.read adjacency w B resources width).run xs).1) =
      HeavyPackingEntry.run adjacency w B resources width := by
  rw [HeavyPackingPrefix.read, FiniteBinaryPrefix.output_law
    (HeavyPackingBitBudget.within_polynomial adjacency w B hw resources width hn hB)
    (HeavyPackingPrefix.binary adjacency w B resources width), HeavyPackingPrefix.ideal_eq]

/-- One constant precedes every graph, stored width, resource word and
coordinate. Both semantic and actual stored widths retain their own premises. -/
theorem uniform_marginal :
    ∀ δ : ℝ, 0 < δ → ∃ K : ℝ, 0 < K ∧
      ∀ (n : ℕ) (adjacency : RetainedGridState.PairFlags n) (w : Row n)
        (B S : ℕ) (_hwidth : ∀ i, (BinaryRational.decode (get w i)).Bounded B)
        (_hstored : ∀ i, BinaryRational.StoredBounded (get w i) S)
        (resources width : Bits) (_hn : value resources = n) (_hB : value width = B)
        (i : Fin n),
      ((FiniteBinaryPrefix.prefixLaw (HeavyPackingBitBudget.polynomial n B S)).toOuterMeasure
        {xs | (HeavyPackingEntry.label
          ((HeavyPackingPrefix.read adjacency w B resources width).run xs).1).any
            (BinaryApproximatePackingSampling.coordinate i) = true}).toReal ≤
        K * (n : ℝ)^((1 : ℝ)/3 + δ) *
          (FractionalCover.value (BinaryApproximatePacking.capacities w) i : ℝ) := by
  intro δ hδ
  obtain ⟨K,hK,h⟩ := HeavyPackingEntry.uniform_marginal δ hδ
  refine ⟨K,hK,?_⟩
  intro n adjacency w B S hwidth hstored resources width hn hB i
  have hi := h n adjacency w B hwidth resources width hn hB i
  rw [← output_law adjacency w B hstored resources width hn hB,
    PMF.toOuterMeasure_map_apply] at hi
  exact hi

end
end DirectedFlowCutGap.HeavyPackingPolynomialLaw
