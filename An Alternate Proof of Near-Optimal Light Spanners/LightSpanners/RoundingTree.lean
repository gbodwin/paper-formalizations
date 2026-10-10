import LightSpanners.Weight

/-! Rounding a bounded-weight spanning tree to unit edges. The factor-two
lightness argument uses the global vertex budget, so it also handles old
tree edges of weight below one half. -/
namespace LightSpanners
open SimpleGraph Finset
variable {V : Type*} [Fintype V]
attribute [local instance] Classical.propDecidable

theorem tree_round_up_weight {T : SimpleGraph V} (hT : T.IsTree)
    (w : Sym2 V → ℝ) (hupper : ∀ e ∈ T.edgeSet, w e ≤ 1) :
    totalWeight T (fun e => max 1 (w e)) = (Fintype.card V : ℝ) - 1 := by
  rw [totalWeight_eq_card_mul T _ 1 (fun e he => max_eq_left (hupper e he)), mul_one]
  have hc : (T.edgeFinset.card : ℝ) + 1 = Fintype.card V := by
    exact_mod_cast hT.card_edgeFinset
  linarith

/-- A spanning tree with edge weights at most one becomes a unit-weight MST
after all graph edges are rounded up to one. No lower tree-edge bound is used. -/
theorem round_up_isMinimumSpanningTree {G T : SimpleGraph V}
    (hT : T.IsTree) (hTG : T ≤ G) (w : Sym2 V → ℝ)
    (hupper : ∀ e ∈ T.edgeSet, w e ≤ 1) :
    IsMinimumSpanningTree G T (fun e => max 1 (w e)) := by
  classical
  apply minimumSpanningTree_of_bottleneck hT hTG
  intro x y _
  obtain ⟨p⟩ := hT.connected x y
  refine ⟨p, fun e he => ?_⟩
  change max 1 (w e) ≤ max 1 (w s(x,y))
  rw [max_eq_left (hupper e (p.edges_subset_edgeSet he))]
  exact le_max_left _ _

/-- Global cardinality, rather than a pointwise lower bound on old edges,
controls the possible loss in lightness from rounding. -/
theorem round_up_lightness_ge_half {G T : SimpleGraph V}
    (hT : T.IsTree) (w : Sym2 V → ℝ)
    (hupper : ∀ e ∈ T.edgeSet, w e ≤ 1)
    (hw : ∀ e ∈ G.edgeSet, 0 ≤ w e) (hpositive : 0 < totalWeight T w)
    (hbudget : (Fintype.card V : ℝ) - 1 ≤ 2 * totalWeight T w) :
    lightness G T w / 2 ≤ lightness G T (fun e => max 1 (w e)) := by
  have hgraph : totalWeight G w ≤ totalWeight G (fun e => max 1 (w e)) :=
    totalWeight_mono_weights G (fun _ _ => le_max_right _ _)
  have htree : totalWeight T w ≤ totalWeight T (fun e => max 1 (w e)) :=
    totalWeight_mono_weights T (fun _ _ => le_max_right _ _)
  have hnewpos : 0 < totalWeight T (fun e => max 1 (w e)) := hpositive.trans_le htree
  have hnewle : totalWeight T (fun e => max 1 (w e)) ≤ 2 * totalWeight T w := by
    rw [tree_round_up_weight hT w hupper]
    exact hbudget
  have hnonneg : 0 ≤ totalWeight G w :=
    sum_nonneg (fun e he => hw e (by simpa using he))
  simp only [lightness, div_div]
  apply (div_le_div_iff₀ (mul_pos hpositive (by norm_num)) hnewpos).mpr
  calc
    _ ≤ totalWeight G w * (2 * totalWeight T w) :=
      mul_le_mul_of_nonneg_left hnewle hnonneg
    _ ≤ _ := by
      rw [mul_comm 2 (totalWeight T w)]
      exact mul_le_mul_of_nonneg_right hgraph (mul_nonneg hpositive.le (by norm_num))

/-- The normalized subdivision vertex bound gives the needed lightness
guarantee even if pre-existing tree edges are arbitrarily light. -/
theorem normalized_round_up_lightness {G T : SimpleGraph V}
    (hT : T.IsTree) (w : Sym2 V → ℝ) (n : ℕ) (hn : 2 ≤ n)
    (hupper : ∀ e ∈ T.edgeSet, w e ≤ 1)
    (hw : ∀ e ∈ G.edgeSet, 0 ≤ w e)
    (hnormal : totalWeight T w = (n : ℝ) - 1)
    (hcard : Fintype.card V ≤ 2 * n - 1) :
    lightness G T w / 2 ≤ lightness G T (fun e => max 1 (w e)) := by
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  apply round_up_lightness_ge_half hT w hupper hw
  · rw [hnormal]; linarith
  · have hsub : 1 ≤ 2 * n := by omega
    have hc : (Fintype.card V : ℝ) ≤ ((2 * n - 1 : ℕ) : ℝ) := by exact_mod_cast hcard
    rw [Nat.cast_sub hsub, Nat.cast_mul] at hc
    norm_num at hc
    rw [hnormal]
    linarith

end LightSpanners
