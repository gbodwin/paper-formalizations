import OnlineReachabilityPreservers.StartingLowerCaps
import OnlineReachabilityPreservers.HalfFiveProjection

/-! Half-five cleaning at prescribed fractions of the starting averages. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

private theorem half_five_opposite_pruned_widths {n p : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) 5) :
    let M := ∑ i, (paths i).length
    HalfBridgeFree (Before (listRegularizedPaths (removeOppositeIntersections paths) (4*M/n) (4*M/p))) 5 := by
  let M := ∑ i, (paths i).length
  let kept := removeOppositeIntersections paths
  have keptSimple (i : Fin p) : (kept i).Nodup :=
    (removeOppositeIntersections_sublist paths i).nodup (simple i)
  have keptFree := removeOppositeIntersections_halfFree simple free

  exact listRegularizedPaths_halfFree_five_of_unique_intersections keptSimple keptFree
    (fun {_ _ _ _} diff xa xb ya yb => removeOppositeIntersections_unique simple free (by decide) diff xa xb ya yb)
    (4*M/n) (4*M/p)

/-- At half cutoff five two lower caps at the starting averages can have
coefficients with sum at most seven fifteenths. Both factor-four upper
caps and both original budgets still hold. -/
theorem regularization_list_half_five_of_starting_lower_caps {n p : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) 5) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    {a b : ℝ} (a0 : 0 ≤ a) (b0 : 0 ≤ b) (aMax : a ≤ 1/4) (bMax : b ≤ 1/4)
    (scale : a+b ≤ 7/15) :
    let M := ∑ i, (paths i).length
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v),
      (∀ i, (rows i).Nodup) ∧ HalfBridgeFree (Before rows) 5 ∧
      M ≤ 930*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧
      (∀ x, a*(M:ℝ)/n ≤ (occurrences (fun i => (rows i).toFinset) x).card ∧
        ((occurrences (fun i => (rows i).toFinset) x).card:ℝ) ≤ 4*(M:ℝ)/n) ∧
      (∀ i, b*(M:ℝ)/p ≤ (rows i).length ∧ ((rows i).length:ℝ) ≤ 4*(M:ℝ)/p) := by
  exact regularization_list_half_of_starting_lower_caps (r := 930) paths simple free (by decide)
    (half_five_opposite_pruned_widths paths simple free) hn hp dense long a0 b0 aMax bMax (by decide)
    (half_pruned_crop_score_of_lower_fractions paths simple free (by decide) (hn.trans_le dense) scale)

/-- The same starting-average bounds hold for distinct nonempty input
and output rows, even when the requested lower length coefficient is zero. -/
theorem regularization_literal_half_five_of_starting_lower_caps {n p : ℕ}
    (paths : Fin p → List (Fin n)) (distinct : Function.Injective paths)
    (valid : ∀ i, paths i ≠ [] ∧ (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) 5) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length)
    {a b : ℝ} (a0 : 0 ≤ a) (b0 : 0 ≤ b) (aMax : a ≤ 1/4) (bMax : b ≤ 1/4)
    (scale : a+b ≤ 7/15) :
    let M := ∑ i, (paths i).length
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v),
      Function.Injective rows ∧ (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧ HalfBridgeFree (Before rows) 5 ∧
      M ≤ 930*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧
      (∀ x, a*(M:ℝ)/n ≤ (occurrences (fun i => (rows i).toFinset) x).card ∧
        ((occurrences (fun i => (rows i).toFinset) x).card:ℝ) ≤ 4*(M:ℝ)/n) ∧
      (∀ i, b*(M:ℝ)/p ≤ (rows i).length ∧ ((rows i).length:ℝ) ≤ 4*(M:ℝ)/p) := by
  have simple (i : Fin p) := (valid i).2
  exact regularization_literal_half_of_starting_lower_caps (r := 930) paths distinct valid free (by decide)
    (half_five_opposite_pruned_widths paths simple free) hn hp dense a0 b0 aMax bMax (by decide)
    (half_pruned_crop_score_of_lower_fractions paths simple free (by decide) (hn.trans_le dense) scale)

end OnlineReachabilityPreservers
