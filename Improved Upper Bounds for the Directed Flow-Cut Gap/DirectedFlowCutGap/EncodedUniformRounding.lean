import DirectedFlowCutGap.EncodedIntegerRounding
import DirectedFlowCutGap.EncodedUniformOutput
import Mathlib.Data.Fintype.Pi

/-!
# Uniformization and retained rounding on the same inputs

The rational preparation is evaluated once. The retained chain graph and
its computed integer cutoff feed the integer program. The returned mask
uses the original labels from that chain.
-/

namespace DirectedFlowCutGap.EncodedUniformRounding

open scoped NNReal
open FiniteDrawTrees RetainedGridState
open EncodedUnitCostReplication EncodedUniformWeightParameters EncodedUniformChain
open FiniteAmplification

private def flagsEquiv (n : ℕ) : Flags n ≃ (Fin n → Bool) where
  toFun mask i := mask[i.val]
  invFun := Vector.ofFn
  left_inv mask := by
    apply Vector.ext
    intro i hi
    simp
  right_inv f := by
    funext i
    simp

@[instance_reducible] def flagsFintype (n : ℕ) : Fintype (Flags n) :=
  Fintype.ofEquiv (Fin n → Bool) (flagsEquiv n).symm

attribute [local instance] flagsFintype

def tree {n : ℕ} (D : Input n) : FiniteDrawTrees.Tree (Flags n) :=
  let p := compute D
  if h : RawNonnegativeRational.Code.one.le p.total = true then
    let chain := materialize p.ports p.average p.counts
    map (EncodedUniformOutput.originalMask chain)
      (EncodedIntegerRounding.tree chain.data.adjacency chain.cutoff
        (expand_cutoff_bounds D h).1)
  else .pure (Vector.replicate n false)

def bitTree {n : ℕ} (T : ℕ) (D : Input n) : FiniteDrawTrees.Tree (Flags n) :=
  LazyFairBitTrees.lower T (tree D)

theorem bitTree_binary {n : ℕ} (T : ℕ) (D : Input n) :
    LazyFairBitTrees.Binary (bitTree T D) := LazyFairBitTrees.lower_binary T _

private theorem tree_expand {n : ℕ} (D : Input n) (h : nontrivial D = true) :
    tree D = map (EncodedUniformOutput.originalMask (expand D))
      (EncodedIntegerRounding.tree (expand D).data.adjacency (expand D).cutoff
        (expand_cutoff_bounds D h).1) := by
  unfold tree
  exact dite_eq_left h

private theorem tree_trivial {n : ℕ} (D : Input n) (h : nontrivial D ≠ true) :
    tree D = .pure (Vector.replicate n false) := by
  unfold tree
  exact dite_eq_right h

private theorem total_pos {n : ℕ} (D : Input n) (h : nontrivial D = true) :
    0 < (compute D).total.realValue := by
  rw [compute_total]
  exact lt_of_lt_of_le (by norm_num) ((nontrivial_iff D).mp h)

theorem support_valid {n : ℕ} (D : Input n) {mask : Flags n}
    (hm : mask ∈ (ideal (tree D)).support) :
    IsIntegralCut D.graph (selectedSet mask) (thresholdDemands D.graph D.weight) := by
  by_cases h : nontrivial D = true
  · rw [tree_expand D h, ideal, law_map] at hm
    obtain ⟨selected, hs, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hm
    have hc := EncodedIntegerRounding.support_valid (expand D).data.adjacency (expand D).cutoff
      (expand_cutoff_bounds D h).1 hs
    exact EncodedUniformOutput.originalMask_correct D (total_pos D h) selected
      (EncodedUniformOutput.integer_cut_correct D h selected hc)
  · rw [tree_trivial D h] at hm
    have he : mask = Vector.replicate n false := by simpa [ideal, law] using hm
    subst mask
    exact (EncodedUniformOutput.trivial_original_output_spec D h).1

theorem bit_support_valid {n : ℕ} (T : ℕ) (D : Input n) {mask : Flags n}
    (hm : mask ∈ (ideal (bitTree T D)).support) :
    IsIntegralCut D.graph (selectedSet mask) (thresholdDemands D.graph D.weight) :=
  support_valid D (LazyFairBitTrees.lowered_support_subset_ideal T (tree D) hm)

def drawBound (n : ℕ) : ℕ := ((6 * n) ^ 3 + 2) * (2 * (6 * n) * (6 * n))

theorem tree_within {n : ℕ} (D : Input n) : Within (drawBound n) (tree D) := by
  by_cases h : nontrivial D = true
  · rw [tree_expand D h]
    apply within_mono (within_map (EncodedIntegerRounding.tree_within ..) _)
    have hn := expand_size_bound D (total_pos D h)
    apply Nat.mul_le_mul
    · unfold IntegerEpochParameters.fuel
      have hlog := Nat.log_le_self (IntegerEpochParameters.restart (expand D).size)
        ((expand D).size ^ 3)
      have hpow := Nat.pow_le_pow_left hn 3
      omega
    · exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 hn) hn
  · rw [tree_trivial D h]
    exact .pure _ _

theorem widths_weaken {A : Type} {t : FiniteDrawTrees.Tree A} {w w' : ℕ}
    (ht : LazyFairBitTrees.WidthsLE w t) (h : w ≤ w') : LazyFairBitTrees.WidthsLE w' t := by
  induction ht with
  | pure a => exact .pure a
  | draw hw _ ih => exact .draw (hw.trans h) ih

theorem sampleWidth_mono {a b L M : ℕ} (h : a ≤ b) (hL : L ≤ M) :
    RetainedDrawTrees.sampleWidth a L ≤ RetainedDrawTrees.sampleWidth b M :=
  LazyFairBitTrees.width_mono (max_le_max (Nat.mul_le_mul h h) hL)

theorem tree_widths {n : ℕ} (D : Input n) :
    LazyFairBitTrees.WidthsLE (RetainedDrawTrees.sampleWidth (6 * n) (3 * n)) (tree D) := by
  by_cases h : nontrivial D = true
  · have hn := expand_size_bound D (total_pos D h)
    have hL : (expand D).cutoff ≤ 3 * n := cutoff_le_ports D h
    rw [tree_expand D h]
    exact widths_weaken (LazyFairBitTrees.widths_map (EncodedIntegerRounding.tree_widths ..) _)
      (sampleWidth_mono hn hL)
  · rw [tree_trivial D h]
    exact .pure _

theorem bitTree_within {n : ℕ} (T : ℕ) (D : Input n) :
    Within (drawBound n * T * RetainedDrawTrees.sampleWidth (6 * n) (3 * n)) (bitTree T D) :=
  LazyFairBitTrees.lower_within (tree_within D) (tree_widths D) T

theorem bit_event_le {n : ℕ} (T : ℕ) (D : Input n) (P : Flags n → Prop) :
    probability (ideal (bitTree T D)) P ≤
      probability (ideal (tree D)) P + (drawBound n : ℝ) * ((1 : ℝ) / 2) ^ T :=
  LazyFairBitTrees.lowered_event_le (tree_within D) T P

private theorem cutoff_scale_le {n : ℕ} (D : Input n) (h : nontrivial D = true) :
    ((expand D).size : ℝ) / ((expand D).cutoff : ℝ) ≤ 2 * (totalWeight D.weight : ℝ) := by
  have he : totalWeight (expand D).data.weight =
      ((expand D).size : ℝ≥0) * (compute D).average.realValue := by
    unfold totalWeight
    simp only [show ∀ i : Fin (expand D).size, (expand D).data.weight i =
        (compute D).average.realValue from fun i => materialize_weight _ _ _ i]
    simp
  have hh : ((expand D).size : ℝ≥0) / ((expand D).cutoff : ℝ≥0) ≤ 2 * totalWeight D.weight := by
    rw [div_eq_mul_inv, ← one_div, expand_cutoff]
    calc
      _ ≤ ((expand D).size : ℝ≥0) * (compute D).average.realValue :=
        mul_le_mul_of_nonneg_left (reciprocal_cutoff_le_average D h) zero_le
      _ = totalWeight (expand D).data.weight := he.symm
      _ ≤ _ := expand_totalWeight_le D (total_pos D h)
  exact_mod_cast hh

theorem expected_size_uniform :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (D : Input n),
        expectedCost (ideal (tree D)) (fun a => ((selectedSet a).card : ℝ)) ≤
          C * ((6 * n : ℕ) : ℝ) ^ ε * (2 * (totalWeight D.weight : ℝ)) ^ (3 / 2 : ℝ) := by
  intro ε hε
  obtain ⟨C, hC, hb⟩ := EncodedIntegerRounding.expected_size_uniform ε hε
  refine ⟨C, hC, ?_⟩
  intro n D
  by_cases h : nontrivial D = true
  · let out := expand D
    let p := EncodedIntegerRounding.tree out.data.adjacency out.cutoff (expand_cutoff_bounds D h).1
    have hi := hb out.size out.data.adjacency out.cutoff (expand_cutoff_bounds D h).1
    rw [expectedCost_map] at hi
    rw [tree_expand D h, ideal, law_map, expectedCost_map]
    calc
      _ ≤ expectedCost (ideal p) (fun a => ((cutSet a).card : ℝ)) := by
        apply Finset.sum_le_sum
        intro a _
        apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
        change ((selectedSet (EncodedUniformOutput.originalMask (expand D) a)).card : ℝ) ≤
          ((selectedSet a).card : ℝ)
        exact_mod_cast EncodedUniformOutput.originalMask_card D a
      _ ≤ C * (out.size : ℝ) ^ ε * AdaptiveCost.sizeFactor (Fin out.size) (out.cutoff : ℝ≥0) := hi
      _ ≤ _ := by
        simp only [AdaptiveCost.sizeFactor, Fintype.card_fin, NNReal.coe_natCast]
        gcongr
        · exact_mod_cast expand_size_bound D (total_pos D h)
        · exact cutoff_scale_le D h
  · rw [tree_trivial D h]
    simp only [ideal, law, expectedCost_pure, (EncodedUniformOutput.trivial_original_output_spec D h).2,
      Nat.cast_zero]
    positivity

end DirectedFlowCutGap.EncodedUniformRounding
