import DirectedFlowCutGap.NormalizedVertexLPRound

/-! Every returned vertex cut has price zero when the normalized optimum is
zero, including tapes below the universally sufficient budget. -/
namespace DirectedFlowCutGap.NormalizedVertexLPZero

open scoped NNReal NNRat ENNReal
open BinaryArithmetic (Bits)
open BinaryFractionalWalkOracle (Adjacency graph)
open BinaryFractionalRows (Row)
open RationalSparsestVertexDistances (weights)
open RationalSparsestVertexThreshold (choose)
open RationalSparsestVertexRound (Result scaled round tree)
open RationalSparsestVertexExpectation (expectedPrice)
open EncodedUnitCostReplication (Input selectedSet)
open RetainedGridState (Flags)
open FiniteDrawTrees (ideal)

attribute [local instance] EncodedUniformRounding.flagsFintype

private theorem round_zero {n : ℕ} (D : Input n) (mode : ChargedVertexModes.Mode) (T : ℕ)
    (free : weightedCost D.cost D.weight = 0) {tape rest : Bits} {mask : Flags n}
    (ran : round D mode T tape = some (mask,rest)) : cutCost D.cost (selectedSet mask) = 0 := by
  have expected : expectedPrice D mode ≤ 0 := by
    cases mode
    · obtain ⟨_,_,uniform⟩ := EncodedWeightedRounding.expected_cost_uniform 1 zero_lt_one
      simpa only [expectedPrice,RationalSparsestVertexRound.tree,ChargedVertexModes.round,free,NNReal.coe_zero,mul_zero] using uniform n D
    · obtain ⟨_,_,uniform⟩ := EncodedSizeRounding.expected_cost_uniform 1 zero_lt_one
      simpa only [expectedPrice,RationalSparsestVertexRound.tree,ChargedVertexModes.round,free,NNReal.coe_zero,mul_zero] using uniform n D
  rw [RationalSparsestVertexRound.round_reference,LiteralTapeComposition.execute] at ran
  obtain ⟨⟨out,receipt⟩,bitsRead,equal⟩ := Option.map_eq_some_iff.mp ran
  have same : out = mask := congrArg Prod.fst equal
  subst out
  have support := LazyFairBitTrees.lowered_support_subset_ideal T (tree D mode)
    (EncodedSolverBits.run_support (LazyFairBitTrees.lower_binary T (tree D mode)) bitsRead)
  exact NNReal.coe_eq_zero.mp (FiniteAmplification.cost_eq_zero_on_support (ideal (tree D mode))
    (fun x => (cutCost D.cost (selectedSet x) : ℝ)) (fun _ => NNReal.coe_nonneg _) expected support)

theorem original_cut_zero {m n : ℕ} (A : Adjacency n) (c : Row n)
    (P : Vector (Fin n × Fin n) m)
    (reach : ∀ j : Fin m, Nonempty (SimplePath (graph A) (P.get j).1 (P.get j).2))
    (T : ℕ) {bits rest : Bits} {mask : Flags n}
    (ran : NormalizedVertexLPRound.run A c P T bits = some (0,.cut mask rest)) :
    cutCost (weights c) (selectedSet mask) = 0 := by
  obtain ⟨⟨q,w⟩,solved,mapped⟩ := Option.bind_eq_some_iff.mp ran
  obtain ⟨result,rounded,equal⟩ := Option.map_eq_some_iff.mp mapped
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj equal
  cases selection : choose A w P with
  | unreachable i =>
    have spec := RationalSparsestVertexThreshold.choose_spec A w P
    rw [selection] at spec
    have path : Nonempty (SimplePath (graph A) P[i.val].1 P[i.val].2) := by
      obtain ⟨i,hi⟩ := i
      exact reach ⟨i,hi⟩
    exact (((vertexDistance_eq_top_iff (graph A) (weights w) _ _).mp spec) path).elim
  | zero => simp [RationalSparsestVertexRound.run,selection] at rounded
  | threshold i τ =>
    rw [RationalSparsestVertexRound.run,selection] at rounded
    obtain ⟨⟨output,tail⟩,performed,same⟩ := Option.map_eq_some_iff.mp rounded
    obtain ⟨rfl,rfl⟩ := Result.cut.inj same
    have price := (NormalizedVertexLP.minimize_attained A c P.get (m : ℚ≥0) reach solved).2.1
    have free : weightedCost (weights c) (weights w) = 0 := by
      apply NNReal.coe_eq_zero.mp
      simpa only [Rat.cast_zero] using price
    have scaledFree : weightedCost (scaled A w c τ).cost (scaled A w c τ).weight = 0 := by
      rw [RationalSparsestVertexRound.scaled_price,RationalSparsestVertexRound.scaled_weight,
        SparsestVertexBridge.weightedCost_div,free,zero_div]
    simpa only [RationalSparsestVertexRound.scaled_price] using
      round_zero (scaled A w c τ) (NormalizedVertexLPRound.pick A w 0 P) T scaledFree performed

end DirectedFlowCutGap.NormalizedVertexLPZero
