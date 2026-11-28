import OnlineReachabilityPreservers.StartingLowerCaps
import OnlineReachabilityPreservers.HalfSixProjection

/-! Half-six cleaning at starting averages after opposite-intersection pruning. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

/-- Both original-width splits preserve half-six exclusion after pruning under full-three exclusion. -/
theorem listRegularizedPaths_halfFree_six_after_opposite_pruning {n p : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) 6) (three : BridgeFree (Before paths) 3) :
    let M := ∑ i, (paths i).length
    HalfBridgeFree (Before (listRegularizedPaths (removeOppositeIntersections paths) (4*M/n) (4*M/p))) 6 := by
  let M := ∑ i, (paths i).length
  let kept := removeOppositeIntersections paths
  have keptSimple (i : Fin p) : (kept i).Nodup :=
    (removeOppositeIntersections_sublist paths i).nodup (simple i)
  have keptFree := removeOppositeIntersections_halfFree simple free

  exact listRegularizedPaths_halfFree_six_of_full_three_unique keptSimple keptFree
    (removeOppositeIntersections_fullFree simple three)
    (fun {_ _ _ _} diff xa xb ya yb => removeOppositeIntersections_unique simple free (by decide) diff xa xb ya yb)
    (4*M/n) (4*M/p)

/-- With full-three exclusion, half-six families permit the same starting
lower fractions after pruning, including with arbitrary original intersections. -/
theorem regularization_list_half_six_of_starting_lower_caps {n p : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) 6) (three : BridgeFree (Before paths) 3) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    {a b : ℝ} (a0 : 0 ≤ a) (b0 : 0 ≤ b) (aMax : a ≤ 1/4) (bMax : b ≤ 1/4)
    (scale : a+b ≤ 7/15) :
    let M := ∑ i, (paths i).length
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v),
      (∀ i, (rows i).Nodup) ∧ HalfBridgeFree (Before rows) 6 ∧
      M ≤ 930*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧
      (∀ x, a*(M:ℝ)/n ≤ (occurrences (fun i => (rows i).toFinset) x).card ∧
        ((occurrences (fun i => (rows i).toFinset) x).card:ℝ) ≤ 4*(M:ℝ)/n) ∧
      (∀ i, b*(M:ℝ)/p ≤ (rows i).length ∧ ((rows i).length:ℝ) ≤ 4*(M:ℝ)/p) := by
  exact regularization_list_half_of_starting_lower_caps (r := 930) paths simple free (by decide)
    (listRegularizedPaths_halfFree_six_after_opposite_pruning paths simple free three) hn hp dense long a0 b0 aMax bMax (by decide)
    (half_pruned_crop_score_of_lower_fractions paths simple free (by decide) (hn.trans_le dense) scale)

/-- The starting lower fractions at half cutoff six also give a
distinct nonempty witness when the input has that form. -/
theorem regularization_literal_half_six_of_starting_lower_caps {n p : ℕ}
    (paths : Fin p → List (Fin n)) (distinct : Function.Injective paths)
    (valid : ∀ i, paths i ≠ [] ∧ (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) 6) (three : BridgeFree (Before paths) 3) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length)
    {a b : ℝ} (a0 : 0 ≤ a) (b0 : 0 ≤ b) (aMax : a ≤ 1/4) (bMax : b ≤ 1/4)
    (scale : a+b ≤ 7/15) :
    let M := ∑ i, (paths i).length
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v),
      Function.Injective rows ∧ (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧ HalfBridgeFree (Before rows) 6 ∧
      M ≤ 930*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧
      (∀ x, a*(M:ℝ)/n ≤ (occurrences (fun i => (rows i).toFinset) x).card ∧
        ((occurrences (fun i => (rows i).toFinset) x).card:ℝ) ≤ 4*(M:ℝ)/n) ∧
      (∀ i, b*(M:ℝ)/p ≤ (rows i).length ∧ ((rows i).length:ℝ) ≤ 4*(M:ℝ)/p) := by
  have simple (i : Fin p) := (valid i).2
  exact regularization_literal_half_of_starting_lower_caps (r := 930) paths distinct valid free (by decide)
    (listRegularizedPaths_halfFree_six_after_opposite_pruning paths simple free three) hn hp dense a0 b0 aMax bMax (by decide)
    (half_pruned_crop_score_of_lower_fractions paths simple free (by decide) (hn.trans_le dense) scale)

/-- At half cutoff six with full-three exclusion, retaining thirteen
twenty-fourths of the mass under opposite pruning pays for all four
exact starting caps. -/
theorem regularization_list_frozen_half_six_after_opposite_pruning {n p : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) 6) (three : BridgeFree (Before paths) 3)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (retained : 13*(∑ i, (paths i).length) ≤ 24*(∑ i, (removeOppositeIntersections paths i).length)) :
    let M := ∑ i, (paths i).length
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v),
      (∀ i, (rows i).Nodup) ∧ HalfBridgeFree (Before rows) 6 ∧
      M ≤ 288*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧ frozenListCaps n p M rows := by
  let M := ∑ i, (paths i).length
  let K := ∑ i, (removeOppositeIntersections paths i).length
  have upper : K ≤ M := sum_le_sum (fun i _ => (removeOppositeIntersections_sublist paths i).length_le)
  have room : ((1/4:ℝ)+1/4+1/((288:ℕ):ℝ))*(M:ℝ) ≤ halfPrunedCropScore M K := by
    rw [show (1/4:ℝ)+1/4 = 1/2 by norm_num]
    exact half_pruned_crop_score_of_large_mass (M := M) (K := K) (hn.trans_le dense) retained upper
  obtain ⟨v,vFit,q,qFit,rows,rowsSimple,rowsFree,retention,within,degree,length⟩ :=
    regularization_list_half_of_starting_lower_caps paths simple free (by decide)
      (listRegularizedPaths_halfFree_six_after_opposite_pruning paths simple free three) hn hp dense long
      (by norm_num) (by norm_num) le_rfl le_rfl (by decide) room
  refine ⟨v,vFit,q,qFit,rows,rowsSimple,rowsFree,retention,within,?_,?_⟩
  · intro x
    exact ⟨by (convert (degree x).1 using 1; ring),(degree x).2⟩
  · intro i
    exact ⟨by (convert (length i).1 using 1; ring),(length i).2⟩

/-- With the same pruning retention, the exact starting caps hold
for distinct, nonempty literal input and output paths. -/
theorem regularization_literal_frozen_half_six_after_opposite_pruning {n p : ℕ}
    (paths : Fin p → List (Fin n)) (distinct : Function.Injective paths)
    (valid : ∀ i, paths i ≠ [] ∧ (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) 6) (three : BridgeFree (Before paths) 3)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length)
    (retained : 13*(∑ i, (paths i).length) ≤ 24*(∑ i, (removeOppositeIntersections paths i).length)) :
    let M := ∑ i, (paths i).length
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v),
      Function.Injective rows ∧ (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧ HalfBridgeFree (Before rows) 6 ∧
      M ≤ 288*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧ frozenListCaps n p M rows := by
  let M := ∑ i, (paths i).length
  by_cases low : M ≤ 8*max n p
  · obtain ⟨v,vFit,q,qFit,rows,oneToOne,rowsValid,full,retention,upper,caps⟩ :=
      regularization_literal_half_full_all_of_low_mass paths distinct valid free (by decide) hn hp dense low
    exact ⟨v,vFit,q,qFit,rows,oneToOne,rowsValid,(full 6).halfFree,by omega,upper,caps⟩
  have long : p ≤ M := calc
    _ = ∑ _ : Fin p, (1:ℕ) := by simp
    _ ≤ _ := sum_le_sum (fun i _ => List.length_pos_of_ne_nil (valid i).1)
  obtain ⟨v,vFit,q,qFit,rows,rowsSimple,rowsFree,retention,upper,caps⟩ :=
    regularization_list_frozen_half_six_after_opposite_pruning paths (fun i => (valid i).2)
      free three hn hp dense long retained
  have mean : 4*p < M := by have bound := le_max_right n p; omega
  obtain ⟨oneToOne,nonempty⟩ :=
    frozen_length_distinct_of_large_mean rowsSimple rowsFree (by decide) hp mean caps
  exact ⟨v,vFit,q,qFit,rows,oneToOne,fun i => ⟨nonempty i,rowsSimple i⟩,rowsFree,retention,upper,caps⟩

end OnlineReachabilityPreservers
