import DirectedFlowCutGap.EncodedWeightedRounding
import DirectedFlowCutGap.EncodedHeavyVertexOutput

/-!
# A size-sensitive rounding program for rational vertex instances

The encoded cube-root threshold selects heavy vertices. The actual weighted
program runs on the retained survivor instance, then the original heavy
vertices and pulled-back survivor mask are combined.
-/

namespace DirectedFlowCutGap.EncodedSizeRounding

open scoped NNReal
open FiniteDrawTrees RetainedGridState FiniteAmplification
open EncodedUnitCostReplication EncodedHeavyVertexPreparation EncodedCubeRootThreshold

attribute [local instance] EncodedUniformRounding.flagsFintype

def tree {n : ℕ} (D : Input n) : FiniteDrawTrees.Tree (Flags n) :=
  let residual := (prepare D).1
  map (combinedMask residual) (EncodedWeightedRounding.tree residual.data)

def bitTree {n : ℕ} (T : ℕ) (D : Input n) : FiniteDrawTrees.Tree (Flags n) :=
  LazyFairBitTrees.lower T (tree D)

theorem support_valid {n : ℕ} (D : Input n) {mask : Flags n}
    (hm : mask ∈ (ideal (tree D)).support) :
    IsIntegralCut D.graph (selectedSet mask) (thresholdDemands D.graph D.weight) := by
  simp only [tree, prepare_value, ideal, law_map] at hm
  obtain ⟨selected, hs, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hm
  exact combinedMask_correct D (threshold n) (threshold_le_quarter n) selected
    (EncodedWeightedRounding.support_valid _ hs)

theorem bit_support_valid {n : ℕ} (T : ℕ) (D : Input n) {mask : Flags n}
    (hm : mask ∈ (ideal (bitTree T D)).support) :
    IsIntegralCut D.graph (selectedSet mask) (thresholdDemands D.graph D.weight) :=
  support_valid D (LazyFairBitTrees.lowered_support_subset_ideal T (tree D) hm)

theorem bitTree_binary {n : ℕ} (T : ℕ) (D : Input n) :
    LazyFairBitTrees.Binary (bitTree T D) := LazyFairBitTrees.lower_binary T _

theorem tree_within {n : ℕ} (D : Input n) :
    Within (EncodedUniformRounding.drawBound (4 * n ^ 2)) (tree D) := by
  simp only [tree, prepare_value]
  apply within_mono (within_map (EncodedWeightedRounding.tree_within _) _)
  unfold EncodedUniformRounding.drawBound
  have hb := build_size_le D (threshold n)
  gcongr

theorem bit_event_le {n : ℕ} (T : ℕ) (D : Input n) (P : Flags n → Prop) :
    probability (ideal (bitTree T D)) P ≤
      probability (ideal (tree D)) P +
        (EncodedUniformRounding.drawBound (4 * n ^ 2) : ℝ) * ((1 : ℝ) / 2) ^ T :=
  LazyFairBitTrees.lowered_event_le (tree_within D) T P

private theorem root_cube (n : ℕ) : ((n : ℝ) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = n := by
  simpa only [one_div, Nat.cast_ofNat] using Real.rpow_inv_natCast_pow
    (Nat.cast_nonneg (α := ℝ) n) (by decide : (3 : ℕ) ≠ 0)

private theorem cube_proxy (n : ℕ) (hn : 0 < n) :
    (n : ℝ) ^ (1 / 3 : ℝ) ≤ (ceilCube n : ℝ) ∧
      (ceilCube n : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 3 : ℝ) := by
  constructor
  · apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by decide : (3 : ℕ) ≠ 0)).mp
    rw [root_cube]
    have h : n ≤ ceilCube n ^ 3 := by simpa [cube, pow_succ] using le_cube_ceilCube n
    exact_mod_cast h
  · apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by decide : (3 : ℕ) ≠ 0)).mp
    rw [mul_pow, root_cube]
    norm_num
    have h : ceilCube n ^ 3 ≤ 8 * n := by simpa [cube, pow_succ] using cube_ceilCube_le n hn
    exact_mod_cast h

private theorem residual_root_le {n : ℕ} (D : Input n) (hn : 0 < n) :
    (totalWeight (build D (threshold n)).data.weight : ℝ) ^ (1 / 2 : ℝ) ≤
      (n : ℝ) ^ (1 / 3 : ℝ) := by
  let x := (n : ℝ) ^ (1 / 3 : ℝ)
  let q := (ceilCube n : ℝ)
  have hq : 0 < q := by
    change (0 : ℝ) < (ceilCube n : ℝ)
    exact_mod_cast ceilCube_positive n
  have hth : ((threshold n).realValue : ℝ) = 1 / (4 * q) := by
    rw [threshold_value, NNReal.coe_div, NNReal.coe_one, NNReal.coe_mul,
      NNReal.coe_ofNat, NNReal.coe_natCast]
  have hw : (totalWeight (build D (threshold n)).data.weight : ℝ) ≤ x ^ 2 := by
    calc
      _ ≤ 2 * (n : ℝ) * ((threshold n).realValue : ℝ) := by
        exact_mod_cast build_totalWeight_le D (threshold n)
      _ = (2 * (n : ℝ)) / (4 * q) := by rw [hth]; ring
      _ ≤ x ^ 2 := by
        apply (div_le_iff₀ (by positivity : 0 < 4 * q)).mpr
        calc
          _ ≤ 4 * (n : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) n]
          _ = x ^ 2 * (4 * x) := by
            rw [← root_cube n]
            change 4 * x ^ (3 : ℕ) = _
            ring
          _ ≤ x ^ 2 * (4 * q) := by
            gcongr
            exact (cube_proxy n hn).1
  apply (Real.rpow_le_rpow (by positivity) hw (by norm_num)).trans_eq
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num [x]

theorem expected_cost_uniform :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧
      ∀ (n : ℕ) (D : Input n),
        expectedCost (ideal (tree D)) (fun a => (cutCost D.cost (selectedSet a) : ℝ)) ≤
          K * (n : ℝ) ^ (1 / 3 + ε) * (weightedCost D.cost D.weight : ℝ) := by
  intro ε hε
  obtain ⟨K, hK, hb⟩ := EncodedWeightedRounding.expected_cost_uniform ε hε
  refine ⟨8 + 2 * K, by positivity, ?_⟩
  intro n D
  by_cases hn : n = 0
  · subst n
    have hzero (a : Flags 0) : cutCost D.cost (selectedSet a) = 0 := by
      unfold cutCost
      exact Finset.sum_eq_zero (fun i _ => Fin.elim0 i)
    simp [expectedCost, hzero, weightedCost]
  · let out := build D (threshold n)
    let p := ideal (EncodedWeightedRounding.tree out.data)
    let x := (n : ℝ) ^ (1 / 3 : ℝ)
    let obj : ℝ := weightedCost D.cost D.weight
    let heavyCost : ℝ := cutCost D.cost (WeightSelfReduction.heavy D.weight (threshold n).realValue)
    have hnReal : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hpow : (1 : ℝ) ≤ (n : ℝ) ^ ε := Real.one_le_rpow
      (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn) hε.le
    have hheavy : heavyCost ≤ 8 * x * obj := by
      have hh := WeightSelfReduction.heavy_cutCost_le D.weight D.cost
        (threshold n).realValue (threshold_positive n)
      rw [div_eq_mul_inv, ← one_div, reciprocal_threshold] at hh
      have hh' : heavyCost ≤ obj * (4 * (ceilCube n : ℝ)) := by exact_mod_cast hh
      calc
        _ ≤ obj * (4 * (ceilCube n : ℝ)) := hh'
        _ ≤ obj * (4 * (2 * x)) := by
          gcongr
          exact (cube_proxy n (Nat.pos_of_ne_zero hn)).2
        _ = _ := by ring
    have hcost (a : Flags out.size) :
        (cutCost D.cost (selectedSet (combinedMask out a)) : ℝ) =
          heavyCost + (cutCost out.data.cost (selectedSet a) : ℝ) := by
      dsimp only [out, heavyCost]
      exact_mod_cast combinedMask_cost D (threshold n) a
    simp only [tree, prepare_value, ideal, law_map, expectedCost_map]
    change expectedCost p (fun a => (cutCost D.cost (selectedSet (combinedMask out a)) : ℝ)) ≤ _
    simp_rw [hcost]
    have hsplit : expectedCost p (fun a => heavyCost + (cutCost out.data.cost (selectedSet a) : ℝ)) =
        heavyCost + expectedCost p (fun a => (cutCost out.data.cost (selectedSet a) : ℝ)) := by
      simp only [expectedCost, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
        sum_probability_toReal, one_mul]
    rw [hsplit]
    calc
      _ ≤ 8 * x * obj +
          (K * (out.size : ℝ) ^ ε * (totalWeight out.data.weight : ℝ) ^ (1 / 2 : ℝ) *
            (weightedCost out.data.cost out.data.weight : ℝ)) :=
        add_le_add hheavy (hb out.size out.data)
      _ ≤ 8 * x * obj + K * (n : ℝ) ^ ε * x * (2 * obj) := by
        have hs : (out.size : ℝ) ≤ n := by exact_mod_cast build_size_le D (threshold n)
        have hw : (weightedCost out.data.cost out.data.weight : ℝ) ≤ 2 * obj := by
          exact_mod_cast build_weightedCost_le D (threshold n)
        gcongr
        exact residual_root_le D (Nat.pos_of_ne_zero hn)
      _ ≤ 8 * x * obj * (n : ℝ) ^ ε + K * (n : ℝ) ^ ε * x * (2 * obj) := by
        have hh : (0 : ℝ) ≤ 8 * x * obj := by dsimp [x, obj]; positivity
        exact add_le_add (le_mul_of_one_le_right hh hpow) le_rfl
      _ = _ := by
        rw [Real.rpow_add hnReal]
        dsimp only [x]
        ring

end DirectedFlowCutGap.EncodedSizeRounding
