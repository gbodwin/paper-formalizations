import DirectedFlowCutGap.EdgeRounding

/-!
# Threshold-preserving removal of tiny edge weights

For `n > 0`, weights at most `1/(2n)` are dropped and the remaining weights
are doubled. The proof uses the strict bound of `n` on the number of edges
of every simple path; it does not assert monotonicity of distances. The total
weight changes to an actual value at most `2W`, which is not identified with
an exact gap parameter at `W`. Normalization by any positive diameter and
the empty-cut case `W < 1` are also proved here.
-/
namespace DirectedFlowCutGap
noncomputable section
open scoped BigOperators NNReal ENNReal
attribute [local instance] Classical.propDecidable

namespace TinyEdgePreprocessing
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Drop all tiny coordinates, double the remaining coordinates. -/
def weight (w : V × V → ℝ≥0) (e : V × V) : ℝ≥0 :=
  if w e ≤ (2 * (Fintype.card V : ℝ≥0))⁻¹ then 0 else 2 * w e

omit [DecidableEq V] in
theorem weight_le_twice (w : V × V → ℝ≥0) (e : V × V) :
    weight w e ≤ 2 * w e := by
  unfold weight
  split_ifs
  · exact zero_le
  · exact le_rfl

omit [DecidableEq V] in
theorem weight_zero_of_tiny (w : V × V → ℝ≥0) (e : V × V)
    (h : w e ≤ (2 * (Fintype.card V : ℝ≥0))⁻¹) : weight w e = 0 := by
  simp only [weight, ite_eq_left h]

omit [DecidableEq V] in
theorem positive_weight_lower (w : V × V → ℝ≥0) (e : V × V)
    (h : 0 < weight w e) : (Fintype.card V : ℝ≥0)⁻¹ ≤ weight w e := by
  have hn : (Fintype.card V : ℝ≥0) ≠ 0 := by
    have : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨e.1⟩
    exact_mod_cast Nat.ne_of_gt this
  by_cases he : w e ≤ (2 * (Fintype.card V : ℝ≥0))⁻¹
  · rw [weight_zero_of_tiny w e he] at h
    exact (lt_irrefl 0 h).elim
  · rw [weight, ite_eq_right he]
    have hh : (2 * (Fintype.card V : ℝ≥0))⁻¹ < w e := lt_of_not_ge he
    have hid : 2 * (2 * (Fintype.card V : ℝ≥0))⁻¹ =
        (Fintype.card V : ℝ≥0)⁻¹ := by field_simp
    rw [← hid]
    exact mul_le_mul_of_nonneg_left hh.le zero_le

omit [DecidableEq V] in
/-- A pointwise charge of one reciprocal node count covers every dropped edge. -/
theorem twice_le_weight_add (w : V × V → ℝ≥0) (e : V × V) :
    2 * w e ≤ weight w e + 2 * (2 * (Fintype.card V : ℝ≥0))⁻¹ := by
  unfold weight
  split_ifs with he
  · simpa using mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ≥0) ≤ 2)
  · exact le_add_of_nonneg_right zero_le

/-- The total dropped charge along a simple path is strictly below one. -/
theorem path_threshold_preserved {G : Digraph V} {s t : V}
    (p : SimplePath G s t) (w : V × V → ℝ≥0) (hp : 1 ≤ p.edgeWeight w) :
    1 ≤ p.edgeWeight (weight w) := by
  have hn : 0 < (Fintype.card V : ℝ≥0) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨s⟩
  have hlen : (p.edgeLength : ℝ≥0) < (Fintype.card V : ℝ≥0) := by
    exact_mod_cast p.edgeLength_lt_card
  have hsum : 2 * p.edgeWeight w ≤ p.edgeWeight (weight w) +
      (p.edgeLength : ℝ≥0) * (2 * (2 * (Fintype.card V : ℝ≥0))⁻¹) := by
    have h := Finset.sum_le_sum (fun e (_ : e ∈ p.edges) => twice_le_weight_add w e)
    simpa [SimplePath.edgeWeight, Finset.mul_sum, Finset.sum_add_distrib] using h
  have hid : 2 * (2 * (Fintype.card V : ℝ≥0))⁻¹ =
      (Fintype.card V : ℝ≥0)⁻¹ := by field_simp
  rw [hid] at hsum
  have hcharge : (p.edgeLength : ℝ≥0) * (Fintype.card V : ℝ≥0)⁻¹ < 1 := by
    rw [← div_eq_mul_inv]
    exact (div_lt_one hn).mpr hlen
  have hsumR := NNReal.coe_le_coe.mpr hsum
  have hchargeR := NNReal.coe_lt_coe.mpr hcharge
  have hpR := NNReal.coe_le_coe.mpr hp
  exact_mod_cast (show (1 : ℝ) ≤ (p.edgeWeight (weight w) : ℝ) by
    push_cast at hsumR hchargeR hpR
    linarith)

/-- Every original threshold demand remains a threshold demand. -/
theorem thresholdDemands_subset (G : Digraph V) (w : V × V → ℝ≥0) :
    edgeThresholdDemands G w ⊆ edgeThresholdDemands G (weight w) := by
  intro st hst
  apply (coe_le_edgeDistance_iff G (weight w) st.1 st.2 1).mpr
  intro p
  exact path_threshold_preserved p w
    ((coe_le_edgeDistance_iff G w st.1 st.2 1).mp hst p)

omit [DecidableEq V] in
/-- The modified total is bounded; equality of the two totals is not assumed. -/
theorem totalWeight_le_twice (G : Digraph V) (w : V × V → ℝ≥0) :
    totalEdgeWeight G (weight w) ≤ 2 * totalEdgeWeight G w := by
  unfold totalEdgeWeight
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun e _ => weight_le_twice w e

/-- If total weight is below one, every threshold pair is already unreachable. -/
theorem threshold_pair_unreachable_of_total_lt_one
    (G : Digraph V) (w : V × V → ℝ≥0) (hW : totalEdgeWeight G w < 1)
    {s t : V} (hst : (s, t) ∈ edgeThresholdDemands G w) :
    ¬Nonempty (SimplePath G s t) := by
  rintro ⟨p⟩
  have hp := (coe_le_edgeDistance_iff G w s t 1).mp hst p
  exact (not_le_of_gt hW) (hp.trans (p.edgeWeight_le_total w))

theorem empty_cut_of_total_lt_one (G : Digraph V) (w : V × V → ℝ≥0)
    (hW : totalEdgeWeight G w < 1) :
    IsIntegralEdgeCut G ∅ (edgeThresholdDemands G w) := by
  intro s t hst p
  exact (threshold_pair_unreachable_of_total_lt_one G w hW hst ⟨p⟩).elim

/-- Normalize a positive target diameter to one. -/
def normalizedWeight (w : V × V → ℝ≥0) (Δ : ℝ≥0) (e : V × V) : ℝ≥0 := w e / Δ

omit [Fintype V] in
theorem path_normalized_weight {G : Digraph V} {s t : V}
    (p : SimplePath G s t) (w : V × V → ℝ≥0) (Δ : ℝ≥0) :
    p.edgeWeight (normalizedWeight w Δ) = p.edgeWeight w / Δ := by
  simp [SimplePath.edgeWeight, normalizedWeight, Finset.sum_div]

omit [DecidableEq V] in
theorem total_normalized_weight (G : Digraph V) (w : V × V → ℝ≥0) (Δ : ℝ≥0) :
    totalEdgeWeight G (normalizedWeight w Δ) = totalEdgeWeight G w / Δ := by
  simp [totalEdgeWeight, normalizedWeight, Finset.sum_div]

omit [Fintype V] in
/-- This equality includes unreachable pairs, whose distance is infinity. -/
theorem normalized_thresholdDemands (G : Digraph V) (w : V × V → ℝ≥0)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) :
    edgeThresholdDemands G (normalizedWeight w Δ) =
      {st | (Δ : ℝ≥0∞) ≤ edgeDistance G w st.1 st.2} := by
  ext st
  change (1 : ℝ≥0∞) ≤ edgeDistance G (normalizedWeight w Δ) st.1 st.2 ↔
    (Δ : ℝ≥0∞) ≤ edgeDistance G w st.1 st.2
  rw [← ENNReal.coe_one, coe_le_edgeDistance_iff, coe_le_edgeDistance_iff]
  simp only [path_normalized_weight, le_div_iff₀ hΔ, one_mul]

end TinyEdgePreprocessing
end
end DirectedFlowCutGap
