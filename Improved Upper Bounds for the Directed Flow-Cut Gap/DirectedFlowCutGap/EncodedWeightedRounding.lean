import DirectedFlowCutGap.EncodedUniformRounding

/-!
# Rounding an actual rational weighted vertex instance

The existing preparation computes the zero-objective mask or retains the
normalized parallel replica. Uniform rounding is executed on that replica
and the selected mask is pulled back through its retained labels.
-/

namespace DirectedFlowCutGap.EncodedWeightedRounding

open scoped NNReal
open FiniteDrawTrees RetainedGridState FiniteAmplification
open EncodedUnitCostReplication EncodedUnitCostPreparation

attribute [local instance] EncodedUniformRounding.flagsFintype

def tree {n : ℕ} (D : Input n) : FiniteDrawTrees.Tree (Flags n) :=
  let r := prepareAndReduce D
  match r.reduced with
  | .zero mask _ => .pure (r.prepared.pullbackMask mask)
  | .replicated _ counts output _ =>
    map (r.prepared.pullbackSample counts output) (EncodedUniformRounding.tree output.input)

def bitTree {n : ℕ} (T : ℕ) (D : Input n) : FiniteDrawTrees.Tree (Flags n) :=
  LazyFairBitTrees.lower T (tree D)

private abbrev replica {n : ℕ} (D : Input n) : Replica (build D).data.counts :=
  materialize (build D).data (build D).data.counts

private theorem tree_zero {n : ℕ} (D : Input n) (hz : (build D).data.totals.objective.num = 0) :
    tree D = .pure ((build D).pullbackMask (build D).data.zeroMask) := by
  unfold tree prepareAndReduce
  dsimp only
  rw [Input.reduce_zero _ hz]

private theorem tree_positive {n : ℕ} (D : Input n) (hC : (build D).data.totals.objective.num ≠ 0) :
    tree D = map ((build D).pullbackSample (build D).data.counts (replica D))
      (EncodedUniformRounding.tree (replica D).input) := by
  unfold tree prepareAndReduce
  dsimp only
  rw [Input.reduce_positive _ hC]

theorem support_valid {n : ℕ} (D : Input n) {mask : Flags n}
    (hm : mask ∈ (ideal (tree D)).support) :
    IsIntegralCut D.graph (selectedSet mask) (thresholdDemands D.graph D.weight) := by
  by_cases h : (build D).data.totals.objective.num = 0
  · rw [tree_zero D h] at hm
    have he : mask = (build D).pullbackMask (build D).data.zeroMask := by simpa [ideal, law] using hm
    subst mask
    exact (zero_output_spec D h).1
  · rw [tree_positive D h, ideal, law_map] at hm
    obtain ⟨selected, hs, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hm
    have hc := EncodedUniformRounding.support_valid (replica D).input hs
    apply pullbackCut_correct D
    exact fullFiberCut_actual_correct (build D).data _ (build D).data.counts_pos selected hc

theorem bit_support_valid {n : ℕ} (T : ℕ) (D : Input n) {mask : Flags n}
    (hm : mask ∈ (ideal (bitTree T D)).support) :
    IsIntegralCut D.graph (selectedSet mask) (thresholdDemands D.graph D.weight) :=
  support_valid D (LazyFairBitTrees.lowered_support_subset_ideal T (tree D) hm)

private theorem input_size_le {n : ℕ} (D : Input n) (h : (build D).data.totals.objective.num ≠ 0) :
    (cloneList (build D).data.counts).length ≤ 4 * n ^ 2 := by
  have hn : 0 < n := by
    by_contra hn
    obtain rfl : n = 0 := by omega
    exact h (empty_objective_zero D)
  exact build_clone_count D hn h

theorem tree_within {n : ℕ} (D : Input n) :
    Within (EncodedUniformRounding.drawBound (4 * n ^ 2)) (tree D) := by
  by_cases h : (build D).data.totals.objective.num = 0
  · rw [tree_zero D h]
    exact .pure _ _
  · rw [tree_positive D h]
    apply within_mono (within_map (EncodedUniformRounding.tree_within (replica D).input) _)
    unfold EncodedUniformRounding.drawBound
    have hs := input_size_le D h
    gcongr

theorem bitTree_binary {n : ℕ} (T : ℕ) (D : Input n) :
    LazyFairBitTrees.Binary (bitTree T D) := LazyFairBitTrees.lower_binary T _

theorem bit_event_le {n : ℕ} (T : ℕ) (D : Input n) (P : Flags n → Prop) :
    probability (ideal (bitTree T D)) P ≤
      probability (ideal (tree D)) P +
        (EncodedUniformRounding.drawBound (4 * n ^ 2) : ℝ) * ((1 : ℝ) / 2) ^ T :=
  LazyFairBitTrees.lowered_event_le (tree_within D) T P

private theorem prepared_objective_pos {n : ℕ} (D : Input n)
    (h : (build D).data.totals.objective.num ≠ 0) :
    0 < weightedCost (build D).data.cost (build D).data.weight := by
  rw [← Input.totals_objective]
  change (0 : ℝ≥0) < ((build D).data.totals.objective.value : ℝ≥0)
  exact_mod_cast (RawNonnegativeRational.Code.value_pos _).mpr (Nat.pos_of_ne_zero h)

private theorem replica_mass_bounds {n : ℕ} (D : Input n)
    (h : (build D).data.totals.objective.num ≠ 0) :
    0 < totalWeight (replica D).input.weight ∧
      totalWeight (replica D).input.weight ≤ 3 * totalWeight D.weight := by
  let c := (build D).data.cost
  let w := (build D).data.weight
  have hc : 0 < weightedCost c w := prepared_objective_pos D h
  have hscale := UnitCostReduction.scale_pos c w hc
  have hmass := UnitCostReduction.scale_objective c w hc
  rw [Input.actual_normalized_totalWeight]
  constructor
  · have hw : 0 < totalWeight w := by
      rw [← hmass]
      positivity
    apply hw.trans_le
    rw [UnitCostReduction.replicatedWeight, VertexReplication.totalWeight_weight]
    apply Finset.sum_le_sum
    intro i _
    exact le_mul_of_one_le_left zero_le (by exact_mod_cast UnitCostReduction.copies_pos _ i)
  · have hb := UnitCostReduction.normalized_copied_weight_le c w hc
    have hh : totalWeight w ≤ 2 * totalWeight D.weight := build_totalWeight_le_double D
    change totalWeight (UnitCostReduction.replicatedWeight c w) ≤ _
    linarith

private theorem pullback_cost_le {n : ℕ} (D : Input n)
    (h : (build D).data.totals.objective.num ≠ 0)
    (selected : Flags (cloneList (build D).data.counts).length) :
    (cutCost D.cost (selectedSet
      ((build D).pullbackSample (build D).data.counts (replica D) selected)) : ℝ) ≤
      ((selectedSet selected).card : ℝ) *
        (6 * (weightedCost D.cost D.weight : ℝ) / (totalWeight (replica D).input.weight : ℝ)) := by
  let W := totalWeight (replica D).input.weight
  let α : ℝ≥0 := ((selectedSet selected).card : ℝ≥0) / W
  have hW : 0 < W := (replica_mass_bounds D h).1
  have hsize : ((selectedSet selected).card : ℝ≥0) ≤ α * W := by
    dsimp only [α]
    rw [div_mul_cancel₀ _ hW.ne']
  have hc := (build D).data.fullFiberCut_cost h α selected hsize
  have hp := mul_le_mul_of_nonneg_left (build_weightedCost_le_double D)
    (show 0 ≤ 3 * α from zero_le)
  have hh : cutCost D.cost (selectedSet
      ((build D).pullbackSample (build D).data.counts (replica D) selected)) ≤
        6 * α * weightedCost D.cost D.weight := by
    change cutCost D.cost ((build D).pullbackCut (fullFiberMask (build D).data.counts
      (labelVector (build D).data.counts) selected)) ≤ _
    rw [pullbackCut_cost]
    exact hc.trans (hp.trans_eq (by ring))
  have hr := NNReal.coe_le_coe.mpr hh
  convert hr using 1
  simp only [α, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_ofNat]
  ring

/-- This is an expected-cost guarantee for the ideal law of the computed
weighted vertex program. The literal bit program has the event error in
`bit_event_le`. -/
theorem expected_cost_uniform :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧
      ∀ (n : ℕ) (D : Input n),
        expectedCost (ideal (tree D)) (fun a => (cutCost D.cost (selectedSet a) : ℝ)) ≤
          K * (n : ℝ) ^ ε * (totalWeight D.weight : ℝ) ^ (1 / 2 : ℝ) *
            (weightedCost D.cost D.weight : ℝ) := by
  intro ε hε
  let δ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨C, hC, hb⟩ := EncodedUniformRounding.expected_size_uniform δ hδ
  refine ⟨6 * C * (2 : ℝ) ^ (3 / 2 : ℝ) * (3 : ℝ) ^ (1 / 2 : ℝ) * (24 : ℝ) ^ δ,
    by positivity, ?_⟩
  intro n D
  by_cases hp : (build D).data.totals.objective.num = 0
  · rw [tree_zero D hp]
    simp only [ideal, law, expectedCost_pure]
    change (cutCost D.cost ((build D).pullbackCut (build D).data.zeroMask) : ℝ) ≤ _
    rw [(zero_output_spec D hp).2]
    positivity
  · let W : ℝ := totalWeight (replica D).input.weight
    let obj : ℝ := weightedCost D.cost D.weight
    let m := (cloneList (build D).data.counts).length
    let p := ideal (EncodedUniformRounding.tree (replica D).input)
    let c : ℝ := 6 * obj / W
    have hW : 0 < W := by exact_mod_cast (replica_mass_bounds D hp).1
    have hc : 0 ≤ c := by dsimp [c, obj]; positivity
    have hN : ((6 * m : ℕ) : ℝ) ≤ 24 * (n : ℝ) ^ 2 := by
      have hn : 6 * m ≤ 24 * n ^ 2 := by
        simpa only [← Nat.mul_assoc] using Nat.mul_le_mul_left 6 (input_size_le D hp)
      exact_mod_cast hn
    have hpower : ((6 * m : ℕ) : ℝ) ^ δ ≤ (24 : ℝ) ^ δ * (n : ℝ) ^ ε := by
      apply (Real.rpow_le_rpow (by positivity) hN hδ.le).trans_eq
      rw [Real.mul_rpow (by norm_num) (by positivity)]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      congr 2
      dsimp [δ]
      ring
    have hmass : W ^ (1 / 2 : ℝ) ≤
        (3 : ℝ) ^ (1 / 2 : ℝ) * (totalWeight D.weight : ℝ) ^ (1 / 2 : ℝ) := by
      have hw : W ≤ 3 * (totalWeight D.weight : ℝ) := by
        exact_mod_cast (replica_mass_bounds D hp).2
      exact (Real.rpow_le_rpow hW.le hw (by norm_num)).trans_eq
        (Real.mul_rpow (by norm_num) (by positivity))
    have hscale : (2 * W) ^ (3 / 2 : ℝ) * c =
        6 * (2 : ℝ) ^ (3 / 2 : ℝ) * W ^ (1 / 2 : ℝ) * obj := by
      have he : W ^ (3 / 2 : ℝ) = W ^ (1 / 2 : ℝ) * W := by
        rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.rpow_add_one hW.ne']
      rw [Real.mul_rpow (by norm_num) hW.le, he]
      dsimp only [c]
      field_simp
    rw [tree_positive D hp, ideal, law_map, expectedCost_map]
    calc
      _ ≤ expectedCost p (fun a => ((selectedSet a).card : ℝ) * c) := by
        apply Finset.sum_le_sum
        intro a _
        exact mul_le_mul_of_nonneg_left (pullback_cost_le D hp a) ENNReal.toReal_nonneg
      _ = expectedCost p (fun a => ((selectedSet a).card : ℝ)) * c := by
        simp only [expectedCost, Finset.sum_mul, mul_assoc]
      _ ≤ (C * ((6 * m : ℕ) : ℝ) ^ δ * (2 * W) ^ (3 / 2 : ℝ)) * c :=
        mul_le_mul_of_nonneg_right (hb m (replica D).input) hc
      _ = 6 * C * (2 : ℝ) ^ (3 / 2 : ℝ) * ((6 * m : ℕ) : ℝ) ^ δ *
          W ^ (1 / 2 : ℝ) * obj := by
        rw [mul_assoc, hscale]
        ring
      _ ≤ _ := by
        calc
          _ ≤ 6 * C * (2 : ℝ) ^ (3 / 2 : ℝ) * ((24 : ℝ) ^ δ * (n : ℝ) ^ ε) *
              ((3 : ℝ) ^ (1 / 2 : ℝ) * (totalWeight D.weight : ℝ) ^ (1 / 2 : ℝ)) * obj := by
            gcongr
          _ = _ := by ring

end DirectedFlowCutGap.EncodedWeightedRounding
