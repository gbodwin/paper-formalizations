import DirectedFlowCutGap.NormalizedOptimalSparsity

/-! An optimal price of zero forces zero cost on every returned cut.
The bounded fair-bit fallback only visits branches of the ideal draw tree. -/
namespace DirectedFlowCutGap.NormalizedOptimalZero

open scoped NNReal NNRat
open BinaryArithmetic (Bits)
open BinaryFractionalWalkOracle (Adjacency graph)
open RationalEdgeThresholds (Weights weights)
open RationalSparsestEdgeRound (Mask scaled round tree)
open EncodedEdgeRounding (selectedEdges expectedPrice)
open FiniteDrawTrees (ideal)

theorem round_ideal_support {n : ℕ} (D : EncodedEdgeGadget.Input n)
    (mode : ChargedVertexModes.Mode) (T : ℕ) {tape rest : Bits} {mask : Mask n}
    (ran : round D mode T tape = some (mask,rest)) : mask ∈ (ideal (tree D mode)).support := by
  rw [RationalSparsestEdgeRound.round_reference, LiteralTapeComposition.execute] at ran
  obtain ⟨⟨result, output⟩, read, equal⟩ := Option.map_eq_some_iff.mp ran
  have same : result = mask := congrArg Prod.fst equal
  subst result
  exact LazyFairBitTrees.lowered_support_subset_ideal T (tree D mode)
    (EncodedSolverBits.run_support (LazyFairBitTrees.lower_binary T (tree D mode)) read)

theorem round_price_zero {n : ℕ} (D : EncodedEdgeGadget.Input n) (mode : ChargedVertexModes.Mode)
    (T : ℕ) {tape rest : Bits} {mask : Mask n}
    (fractional : weightedEdgeCost D.graph D.cost D.weight = 0)
    (ran : round D mode T tape = some (mask,rest)) :
    edgeCutCost D.graph D.cost (selectedEdges mask) = 0 := by
  let p := RationalSparsestEdgeExpectation.law D mode
  let cost (X : Finset (Fin n × Fin n)) : ℝ := edgeCutCost D.graph D.cost X
  have expected : FiniteAmplification.expectedCost p cost ≤ 0 := by
    change expectedPrice D (fun r => ChargedVertexModes.round r mode) ≤ 0
    cases mode
    · obtain ⟨_,_,bound⟩ := EncodedEdgeRounding.mass_expected_uniform 1 zero_lt_one
      simpa only [ChargedVertexModes.round, fractional, NNReal.coe_zero, mul_zero] using bound n D
    · obtain ⟨_,_,bound⟩ := EncodedEdgeRounding.size_expected_uniform 1 zero_lt_one
      simpa only [ChargedVertexModes.round, fractional, NNReal.coe_zero, mul_zero] using bound n D
  have seen : selectedEdges mask ∈ p.support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨mask, round_ideal_support D mode T ran, rfl⟩
  have free := FiniteAmplification.cost_eq_zero_on_support p cost
    (fun _ => NNReal.coe_nonneg _) expected seen
  exact NNReal.coe_eq_zero.mp free

theorem optimal_cut_price_zero {m n : ℕ} (A : Adjacency n) (c : Weights n)
    (pairs : Vector (Fin n × Fin n) m)
    (reachable : ∀ j : Fin m, Nonempty (SimplePath (graph A) pairs[j.val].1 pairs[j.val].2))
    (mode : ChargedVertexModes.Mode) (T : ℕ) {tape rest : Bits} {mask : Mask n}
    (ran : NormalizedEdgeLPRound.runOptimal A c pairs mode T tape = some (0,.cut mask rest)) :
    edgeCutCost (graph A) (weights c) (selectedEdges mask) = 0 := by
  obtain ⟨⟨q,w⟩, solved, mapped⟩ := Option.bind_eq_some_iff.mp ran
  obtain ⟨result, rounded, equal⟩ := Option.map_eq_some_iff.mp mapped
  have price : q = 0 := congrArg Prod.fst equal
  have shape : result = .cut mask rest := congrArg Prod.snd equal
  subst q result
  cases selected : RationalSparsestEdgeThreshold.choose A w pairs with
  | unreachable i =>
    have spec := RationalSparsestEdgeThreshold.choose_spec A w pairs
    rw [selected] at spec
    exact (((edgeDistance_eq_top_iff (graph A) (weights w) _ _).mp spec) (reachable i)).elim
  | zero =>
    simp only [RationalSparsestEdgeRound.run, selected, Option.some.injEq] at rounded
    cases rounded
  | threshold i τ =>
    rw [RationalSparsestEdgeRound.run, selected] at rounded
    obtain ⟨⟨output, suffix⟩, performed, same⟩ := Option.map_eq_some_iff.mp rounded
    obtain ⟨rfl, rfl⟩ := RationalSparsestEdgeRound.Result.cut.inj same
    have optimum := (NormalizedEdgeLP.minimize_attained A c pairs.get (m : ℚ≥0) reachable solved).2.1
    have free : weightedEdgeCost (graph A) (weights c) (weights w) = 0 := by
      apply NNReal.coe_eq_zero.mp
      simpa only [Rat.cast_zero] using optimum
    have scaledFree : weightedEdgeCost (scaled A w c τ).graph
        (scaled A w c τ).cost (scaled A w c τ).weight = 0 := by
      rw [RationalSparsestEdgeRound.scaled_graph, RationalSparsestEdgeRound.scaled_price,
        RationalSparsestEdgeRound.scaled_weight, SparsestEdgeBridge.weightedEdgeCost_div, free, zero_div]
    simpa only [RationalSparsestEdgeRound.scaled_graph, RationalSparsestEdgeRound.scaled_price]
      using round_price_zero (scaled A w c τ) mode T scaledFree performed

end DirectedFlowCutGap.NormalizedOptimalZero
