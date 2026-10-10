import DirectedFlowCutGap.BinaryHeavyProviderTrees

/-! A finite uniform bit budget for every current cost row. Only the original
vertex count and repetition count occur; the actual transformed dimensions
are bounded by the already proved retained weighted-reduction envelope.
This finite maximum is not yet simplified to a polynomial or charged as a
budget-construction algorithm. -/
namespace DirectedFlowCutGap.HeavyQueryBitBudget
noncomputable section
open FiniteDrawTrees LazyFairBitTrees BinaryArithmetic
open EncodedUnitCostReplication EncodedWeightedVertexQuery BinarySamplerMetadata

/-- Finite maximum over every possible retained transformed dimension/cutoff. -/
def bound (n extra : ℕ) : ℕ :=
  (Finset.range (24*n^2+1)).sup fun N =>
    (Finset.range (N+1)).sup fun L =>
      (extra+1)*BinaryEntryTrees.budget N (StatefulBoundedRoundingQuality.canonicalFuel N) L.bits

theorem ready_le {n m : ℕ} {D : Input m} (r : Ready D) (hm : 0<m)
    (hmn : m≤n) (extra : ℕ) : BinaryWeightedTrees.readyBudget r extra≤bound n extra := by
  obtain ⟨hN,hL,_⟩ := r.envelope hm
  have hs : r.chain.size≤24*n^2 := hN.trans (Nat.mul_le_mul_left 24 (Nat.pow_le_pow_left hmn 2))
  unfold BinaryWeightedTrees.readyBudget bound
  exact (Finset.le_sup (f := fun L => (extra+1)*BinaryEntryTrees.budget r.chain.size
      (StatefulBoundedRoundingQuality.canonicalFuel r.chain.size) L.bits)
      (Finset.mem_range.mpr (by omega : r.chain.cutoff<r.chain.size+1))).trans
    (Finset.le_sup (f := fun N => (Finset.range (N+1)).sup fun L =>
      (extra+1)*BinaryEntryTrees.budget N (StatefulBoundedRoundingQuality.canonicalFuel N) L.bits)
      (Finset.mem_range.mpr (by omega : r.chain.size<24*n^2+1)))

theorem weighted_le {n m : ℕ} (D : Input m) (hm : 0<m) (hmn : m≤n) (extra : ℕ) :
    BinaryWeightedTrees.budget D extra≤bound n extra := by
  unfold BinaryWeightedTrees.budget
  cases h : prepare D with
  | inl done => exact Nat.zero_le _
  | inr r => exact ready_le r hm hmn extra

theorem heavy_le {n : ℕ} (D : Input n) (extra : ℕ) :
    BinaryHeavyPrefix.budget D extra≤bound n extra := by
  unfold BinaryHeavyPrefix.budget
  split_ifs with hz
  · exact Nat.zero_le _
  · exact weighted_le (StatefulHeavyQuery.residual D).data (Nat.pos_of_ne_zero hz)
      (EncodedHeavyVertexPreparation.build_size_le D (EncodedCubeRootThreshold.threshold n)) extra

theorem provider_within {n : ℕ} (adjacency : RetainedGridState.PairFlags n)
    (w c : BinaryFractionalRows.Row n) (extra : ℕ) (state : Ledger) :
    Within (bound n extra) (BinaryHeavyProviderTrees.draw adjacency w extra state c) :=
  within_mono (BinaryHeavyProviderTrees.within adjacency w c extra state)
    (heavy_le (HeavyCutProvider.input adjacency w c) extra)

end
end DirectedFlowCutGap.HeavyQueryBitBudget
