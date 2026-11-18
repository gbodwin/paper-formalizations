import DirectedFlowCutGap.EncodedCutSelection
import DirectedFlowCutGap.EncodedSizeRounding
import DirectedFlowCutGap.FractionalCoverRawGuesses

/-!
# Vertex solver from rational graph input to an integral cut

The solver uses the actual fractional cover dispatcher. The zero-objective
and infeasible branches return immediately. In the positive branch each
returned cover supplies one run of the selected encoded rounding program,
and a rational cost comparison returns the cheapest sampled mask.
-/

namespace DirectedFlowCutGap.EncodedVertexSolver

open scoped NNReal
open FiniteDrawTrees FiniteAmplification RetainedGridState
open FractionalCoverRawCore FractionalCoverRawGraph FractionalCoverRawGuesses
open EncodedUnitCostReplication EncodedCutSelection

attribute [local instance] EncodedUniformRounding.flagsFintype

abbrev GraphInput := FractionalCoverRawGraph.Input
abbrev RoundingInput := EncodedUnitCostReplication.Input

def roundingInput {n : ℕ} (D : GraphInput n) (weights : RawRow n) : RoundingInput n :=
  ⟨D.adjacency, weights, D.costs⟩

def maskOfSet {n : ℕ} (X : Finset (Fin n)) : Flags n :=
  Vector.ofFn (fun v => decide (v ∈ X))

theorem selectedSet_maskOfSet {n : ℕ} (X : Finset (Fin n)) :
    selectedSet (maskOfSet X) = X := by
  ext v
  simp [selectedSet, maskOfSet]

inductive Output (n : ℕ) where
  | infeasible (demand : FractionalCoverRawGraph.Pair n)
  | cut (mask : Flags n)
  | invalid

private def finish {n : ℕ} (result : Option (Flags n)) : Output n :=
  result.elim .invalid .cut

abbrev Rounding (n : ℕ) := RoundingInput n → FiniteDrawTrees.Tree (Flags n)

def tree {n : ℕ} (D : GraphInput n) (round : Rounding n) :
    FiniteDrawTrees.Tree (Output n) :=
  match solveInput D with
  | .infeasible d => .pure (.infeasible d)
  | .zero X => .pure (.cut (maskOfSet X))
  | .invalid => .pure .invalid
  | .covers states =>
    map finish (best D.costs (states.map (fun s => round (roundingInput D s.best))))

def bitTree {n : ℕ} (T : ℕ) (D : GraphInput n) (round : Rounding n) :
    FiniteDrawTrees.Tree (Output n) :=
  LazyFairBitTrees.lower T (tree D round)

def massBitTree {n : ℕ} (T : ℕ) (D : GraphInput n) : FiniteDrawTrees.Tree (Output n) :=
  bitTree T D EncodedWeightedRounding.tree

def sizeBitTree {n : ℕ} (T : ℕ) (D : GraphInput n) : FiniteDrawTrees.Tree (Output n) :=
  bitTree T D EncodedSizeRounding.tree

def Valid {n : ℕ} (D : GraphInput n) : Output n → Prop
  | .infeasible _ => ¬ ∃ w : Fin n → ℝ≥0, IsFractionalCut D.graph w {d | d ∈ D.demands}
  | .cut mask => IsIntegralCut D.graph (selectedSet mask) {d | d ∈ D.demands}
  | .invalid => False

theorem comparator_feasible {n : ℕ} (D : GraphInput n) (w : Fin n → ℝ≥0)
    (hw : IsFractionalCut D.graph w {d | d ∈ D.demands}) :
    FractionalCover.RealFeasible (FractionalCoverGraphOracle.columns D.graph D.demands)
      (fun i => (w i : ℝ)) := by
  refine ⟨fun i => (w i).property, ?_⟩
  rintro p ⟨d, hd, q, rfl⟩
  have h := (isFractionalCut_iff D.graph w _).mp hw d.1 d.2 hd q
  simpa [SimplePath.weight, NNReal.coe_sum] using NNReal.coe_le_coe.mpr h

private theorem decode_value_real {n : ℕ} (y : RawRow n) (i : Fin n) :
    (FractionalCover.value (decodeRow y) i : ℝ) = ((get y i).realValue : ℝ) := by
  rw [decode_value, rational, RawNonnegativeRational.Code.realValue]
  exact (Rat.cast_nnratCast _).trans (Nonneg.coe_nnratCast _).symm

theorem cover_feasible {n : ℕ} (D : GraphInput n) (y : RawRow n)
    (hy : FractionalCover.Feasible (FractionalCoverGraphOracle.columns D.graph D.demands) (decodeRow y)) :
    IsFractionalCut D.graph (roundingInput D y).weight {d | d ∈ D.demands} := by
  have hc := FractionalCoverGraphOracle.feasible_isFractionalCut D.graph D.demands (decodeRow y) hy
  have he : (roundingInput D y).weight =
      FractionalCoverGraphOracle.realWeights (decodeRow y) hy.1 := by
    funext i
    apply Subtype.ext
    exact (decode_value_real y i).symm
  rwa [he]

theorem support_valid {n : ℕ} (D : GraphInput n) (round : Rounding n)
    (hround : ∀ (r : RoundingInput n) (a : Flags n), a ∈ (ideal (round r)).support →
      IsIntegralCut r.graph (selectedSet a) (thresholdDemands r.graph r.weight))
    {out : Output n} (hout : out ∈ (ideal (tree D round)).support) : Valid D out := by
  have h := solveInput_correct D
  cases hs : solveInput D with
  | infeasible d =>
    have he : out = .infeasible d := by simpa [tree, hs, ideal, law] using hout
    subst out
    simp only [Correct, hs, decodeOutput] at h
    rintro ⟨w, hw⟩
    exact h ⟨_, comparator_feasible D w hw⟩
  | zero X =>
    have he : out = .cut (maskOfSet X) := by simpa [tree, hs, ideal, law] using hout
    subst out
    simp only [Correct, hs, decodeOutput] at h
    simpa only [Valid, selectedSet_maskOfSet] using h.1
  | invalid =>
    exact (solveInput_not_invalid D hs).elim
  | covers states =>
    simp only [Correct, hs, decodeOutput] at h
    simp only [tree, hs, ideal, law_map] at hout
    obtain ⟨result, hr, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
    cases result with
    | none =>
      have he := (best_none_iff D.costs _).mp hr
      have hnil : states = [] := List.map_eq_nil_iff.mp he
      simp [hnil] at h
    | some mask =>
      obtain ⟨t, ht, hm⟩ := best_support D.costs _ hr
      obtain ⟨state, hstate, rfl⟩ := List.mem_map.mp ht
      have hfeasible := h.2.1 (decodeState state) (List.mem_map.mpr ⟨state, hstate, rfl⟩)
      have hf := cover_feasible D state.best hfeasible
      have hc := hround _ _ hm
      intro s t hst
      exact hc s t (hf s t hst)

theorem massBit_support_valid {n : ℕ} (T : ℕ) (D : GraphInput n) {out : Output n}
    (hout : out ∈ (ideal (massBitTree T D)).support) : Valid D out :=
  support_valid D EncodedWeightedRounding.tree
    (fun r _ hr => EncodedWeightedRounding.support_valid r hr)
    (LazyFairBitTrees.lowered_support_subset_ideal T (tree D EncodedWeightedRounding.tree) hout)

theorem sizeBit_support_valid {n : ℕ} (T : ℕ) (D : GraphInput n) {out : Output n}
    (hout : out ∈ (ideal (sizeBitTree T D)).support) : Valid D out :=
  support_valid D EncodedSizeRounding.tree
    (fun r _ hr => EncodedSizeRounding.support_valid r hr)
    (LazyFairBitTrees.lowered_support_subset_ideal T (tree D EncodedSizeRounding.tree) hout)

theorem bitTree_binary {n : ℕ} (T : ℕ) (D : GraphInput n) (round : Rounding n) :
    LazyFairBitTrees.Binary (bitTree T D round) := LazyFairBitTrees.lower_binary T _

def drawBound {n : ℕ} (D : GraphInput n) (roundBound : ℕ) : ℕ :=
  (FractionalCoverGuesses.gridSteps n (inputWidth D.costs) + 1) * roundBound

theorem tree_within {n : ℕ} (D : GraphInput n) (round : Rounding n) (roundBound : ℕ)
    (hround : ∀ r : RoundingInput n, Within roundBound (round r)) :
    Within (drawBound D roundBound) (tree D round) := by
  cases hs : solveInput D with
  | infeasible d => rw [tree, hs]; exact .pure _ _
  | zero X => rw [tree, hs]; exact .pure _ _
  | invalid => rw [tree, hs]; exact .pure _ _
  | covers states =>
    have hc := solveInput_correct D
    simp only [Correct, hs, decodeOutput, List.length_map] at hc
    rw [tree, hs, drawBound, ← hc.1]
    have hb := best_within D.costs (states.map (fun s => round (roundingInput D s.best)))
      roundBound (by rintro _ h; obtain ⟨s, _, rfl⟩ := List.mem_map.mp h; exact hround _)
    simp only [List.length_map] at hb
    exact within_map hb finish

noncomputable def capacity {n : ℕ} (D : GraphInput n) (i : Fin n) : ℝ≥0 :=
  (get D.costs i).realValue

def outputMask {n : ℕ} : Output n → Option (Flags n)
  | .cut mask => some mask
  | .infeasible _ | .invalid => none

noncomputable def expectedPrice {n : ℕ} (D : GraphInput n) (round : Rounding n) : ℝ :=
  expectedCost ((ideal (tree D round)).map outputMask) (optionPrice D.costs)

private def outputEquiv (n : ℕ) :
    Output n ≃ Option (FractionalCoverRawGraph.Pair n ⊕ Flags n) where
  toFun
    | .infeasible d => some (.inl d)
    | .cut m => some (.inr m)
    | .invalid => none
  invFun
    | some (.inl d) => .infeasible d
    | some (.inr m) => .cut m
    | none => .invalid
  left_inv out := by cases out <;> rfl
  right_inv out := by
    rcases out with _ | (_ | _) <;> rfl

local instance (n : ℕ) : Fintype (Output n) :=
  Fintype.ofEquiv _ (outputEquiv n).symm

noncomputable def outputPrice {n : ℕ} (D : GraphInput n) (out : Output n) : ℝ :=
  optionPrice D.costs (outputMask out)

theorem bit_bad_cost_le {n : ℕ} (T : ℕ) (D : GraphInput n) (round : Rounding n)
    (roundBound : ℕ) (hround : ∀ r : RoundingInput n, Within roundBound (round r))
    (B : ℝ) (hB : 0 < B) (hcost : expectedPrice D round ≤ B) :
    probability (ideal (bitTree T D round)) (fun out => 2 * B < outputPrice D out) ≤
      (1 : ℝ) / 2 + (drawBound D roundBound : ℝ) * ((1 : ℝ) / 2) ^ T := by
  have he := LazyFairBitTrees.lowered_event_le (tree_within D round roundBound hround) T
    (fun out => 2 * B < outputPrice D out)
  have hnonneg (out : Output n) : 0 ≤ outputPrice D out := by
    cases out <;> simp [outputPrice, outputMask, optionPrice, cutPrice]
  rw [expectedPrice, expectedCost_map] at hcost
  have hb := probability_cost_gt_twice_le_half (ideal (tree D round)) (outputPrice D)
    hnonneg hB hcost
  exact he.trans (add_le_add hb le_rfl)

private theorem decode_cost {n : ℕ} (c y : RawRow n) :
    (FractionalCover.objective (decodeRow c) (decodeRow y) : ℝ) =
      (weightedCost (fun i => (get c i).realValue) (fun i => (get y i).realValue) : ℝ) := by
  simp only [FractionalCover.objective, weightedCost, Rat.cast_sum, NNReal.coe_sum,
    Rat.cast_mul, NNReal.coe_mul, decode_value_real]

private theorem decode_zero_price {n : ℕ} (c : RawRow n) (X : Finset (Fin n))
    (h : ∑ i ∈ X, FractionalCover.value (decodeRow c) i = 0) :
    cutPrice c (maskOfSet X) = 0 := by
  unfold cutPrice cutCost
  rw [selectedSet_maskOfSet, NNReal.coe_sum]
  have hh := congrArg (fun x : ℚ => (x : ℝ)) h
  simpa only [Rat.cast_sum, Rat.cast_zero, decode_value_real] using hh

/-- The optimum comparison uses a single returned cover which meets both
bicriteria inequalities. The minimum is taken over the actual sampled cuts. -/
private theorem expected_comparison {n : ℕ} (D : GraphInput n) (round : Rounding n)
    (w : Fin n → ℝ≥0) (hw : IsFractionalCut D.graph w {d | d ∈ D.demands})
    (B : ℝ) (hB : 0 ≤ B)
    (bound : ∀ y : RawRow n,
      (weightedCost (capacity D) (roundingInput D y).weight : ℝ) ≤
        6 * (weightedCost (capacity D) w : ℝ) →
      (totalWeight (roundingInput D y).weight : ℝ) ≤ 12 * (totalWeight w : ℝ) →
      expectedCost (ideal (round (roundingInput D y))) (cutPrice D.costs) ≤ B) :
    expectedPrice D round ≤ B := by
  have hc := solveInput_correct D
  have hf := comparator_feasible D w hw
  cases hs : solveInput D with
  | infeasible d =>
    simp only [Correct, hs, decodeOutput] at hc
    exact (hc ⟨_, hf⟩).elim
  | invalid => exact (solveInput_not_invalid D hs).elim
  | zero X =>
    simp only [Correct, hs, decodeOutput] at hc
    simp only [expectedPrice, tree, hs, ideal, law, PMF.pure_map, expectedCost_pure, outputMask,
      optionPrice, Option.elim_some, decode_zero_price D.costs X hc.2]
    exact hB
  | covers states =>
    simp only [Correct, hs, decodeOutput] at hc
    obtain ⟨s, hmem, _, hprice, hmass⟩ := hc.2.2 (fun i => (w i : ℝ)) hf
    obtain ⟨state, hin, rfl⟩ := List.mem_map.mp hmem
    simp only [expectedPrice, tree, hs, ideal, law_map, PMF.map_comp]
    have he : (outputMask : Output n → Option (Flags n)) ∘ finish = id := by
      funext x
      cases x <;> rfl
    rw [he, PMF.map_id]
    refine (expected_best_le D.costs _ (List.mem_map.mpr ⟨state, hin, rfl⟩)).trans (bound state.best ?_ ?_)
    · change (weightedCost (fun i => (get D.costs i).realValue)
        (fun i => (get state.best i).realValue) : ℝ) ≤ _
      rw [← decode_cost]
      simpa only [decodeState, capacity, weightedCost, NNReal.coe_sum, NNReal.coe_mul,
        decode_value_real] using hprice
    · change ((∑ i, (get state.best i).realValue : ℝ≥0) : ℝ) ≤ _
      simpa only [decodeState, totalWeight, NNReal.coe_sum, decode_value_real] using hmass

theorem size_expected_uniform :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧
      ∀ (n : ℕ) (D : GraphInput n) (w : Fin n → ℝ≥0),
        IsFractionalCut D.graph w {d | d ∈ D.demands} →
        expectedPrice D EncodedSizeRounding.tree ≤
          K * (n : ℝ) ^ (1 / 3 + ε) * (weightedCost (capacity D) w : ℝ) := by
  intro ε hε
  obtain ⟨K, hK, hround⟩ := EncodedSizeRounding.expected_cost_uniform ε hε
  refine ⟨6 * K, by positivity, ?_⟩
  intro n D w hw
  apply expected_comparison D EncodedSizeRounding.tree w hw _ (by positivity)
  intro y hcost _
  apply (hround n (roundingInput D y)).trans
  calc
    _ ≤ K * (n : ℝ) ^ (1 / 3 + ε) * (6 * (weightedCost (capacity D) w : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hcost (by positivity)
    _ = _ := by ring

theorem mass_expected_uniform :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧
      ∀ (n : ℕ) (D : GraphInput n) (w : Fin n → ℝ≥0),
        IsFractionalCut D.graph w {d | d ∈ D.demands} →
        expectedPrice D EncodedWeightedRounding.tree ≤
          K * (n : ℝ) ^ ε * (totalWeight w : ℝ) ^ (1 / 2 : ℝ) *
            (weightedCost (capacity D) w : ℝ) := by
  intro ε hε
  obtain ⟨K, hK, hround⟩ := EncodedWeightedRounding.expected_cost_uniform ε hε
  refine ⟨6 * (12 : ℝ) ^ (1 / 2 : ℝ) * K, by positivity, ?_⟩
  intro n D w hw
  apply expected_comparison D EncodedWeightedRounding.tree w hw _ (by positivity)
  intro y hcost hmass
  apply (hround n (roundingInput D y)).trans
  have hroot : (totalWeight (roundingInput D y).weight : ℝ) ^ (1 / 2 : ℝ) ≤
      (12 : ℝ) ^ (1 / 2 : ℝ) * (totalWeight w : ℝ) ^ (1 / 2 : ℝ) :=
    (Real.rpow_le_rpow (by positivity) hmass (by norm_num)).trans_eq
      (Real.mul_rpow (by norm_num) (by positivity))
  calc
    _ ≤ K * (n : ℝ) ^ ε * ((12 : ℝ) ^ (1 / 2 : ℝ) * (totalWeight w : ℝ) ^ (1 / 2 : ℝ)) *
        (6 * (weightedCost (capacity D) w : ℝ)) := by
      have hcost' : (weightedCost (roundingInput D y).cost (roundingInput D y).weight : ℝ) ≤
          6 * (weightedCost (capacity D) w : ℝ) := hcost
      gcongr
    _ = _ := by ring

end DirectedFlowCutGap.EncodedVertexSolver
