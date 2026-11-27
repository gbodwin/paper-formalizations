import OnlineReachabilityPreservers.LocalFrozenCleaning

/-! Peel inside a rectangle that already has capped degrees and lengths. -/

namespace OnlineReachabilityPreservers

open Finset

/-- If the mass inside a rectangle pays the original peeling thresholds
and the specified retention, preserve the chosen bridge condition and
both budgets with the four original-average caps. -/
theorem regularization_list_frozen_of_capped_rectangle {I V : Type*}
    [LinearOrder I] [Fintype I] [LinearOrder V] [Fintype V] {n p M cutoff retention : ℕ} {half : Bool}
    (pieces : I → List V) (simple : ∀ i, (pieces i).Nodup) (allowed : localOrderAdmissible half cutoff pieces)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ M) (long : p ≤ M) (ret : 0 < retention)
    (length : ∀ i, (pieces i).length ≤ 4*M/p)
    (degree : ∀ v, (occurrences (fun i => (pieces i).toFinset) v).card ≤ 4*M/n)
    (upper : (∑ i, (pieces i).length) ≤ M)
    (A : Finset V) (B : Finset I) (va : A.card ≤ n) (pa : B.card ≤ p)
    (enough : (M:ℝ)/retention + (M:ℝ)/(4*(n:ℝ))*A.card + (M:ℝ)/(4*(p:ℝ))*B.card ≤
      ((∑ i ∈ B, ((pieces i).toFinset ∩ A).card : ℕ):ℝ)) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half cutoff clean ∧
      M ≤ retention*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let kept := restrictListPaths pieces A B
  have keptSimple (i : B) : (kept i).Nodup := restrictListPath_nodup (simple i.val) A
  have keptAllowed : localOrderAdmissible half cutoff kept := by
    cases half
    · exact restrictListPaths_fullFree simple allowed A B
    · exact restrictListPaths_halfFree simple allowed A B
  have each (i : B) : (kept i).length = ((pieces i.val).toFinset ∩ A).card :=
    restrictListPath_length (simple i.val) A
  have keptLength (i : B) : (kept i).length ≤ 4*M/p :=
    (each i).le.trans ((card_le_card inter_subset_left).trans ((List.toFinset_card_le _).trans (length i.val)))
  have keptDegree (v : A) : (occurrences (fun i => (kept i).toFinset) v).card ≤ 4*M/n := by
    have same : (fun i => (kept i).toFinset) = rectanglePaths (fun i => (pieces i).toFinset) A B :=
      funext (restrictListPaths_toFinset pieces A B)
    rw [same]
    exact (rectanglePaths_degree_le (fun i => (pieces i).toFinset) A B v).trans (degree v.val)
  have mass : (∑ i, (kept i).length) = ∑ i ∈ B, ((pieces i).toFinset ∩ A).card := by
    rw [← sum_attach B (fun i => ((pieces i).toFinset ∩ A).card)]
    exact sum_congr rfl (fun i _ => each i)
  have keptUpper : (∑ i, (kept i).length) ≤ M := by
    rw [mass]
    exact (sum_le_sum fun i (_ : i ∈ B) => (card_le_card inter_subset_left).trans (List.toFinset_card_le _)).trans
      ((sum_le_sum_of_subset (subset_univ B)).trans upper)
  have counted : (∑ v : A, (occurrences (fun i => (kept i).toFinset) v).card) =
      ∑ i ∈ B, ((pieces i).toFinset ∩ A).card := by
    rw [sum_occurrences,← mass]
    exact sum_congr rfl fun i _ => List.toFinset_card_of_nodup (keptSimple i)
  apply regularization_list_frozen_after_kept_vertices (half := half) kept keptSimple keptAllowed
    hn hp dense long ret (univ : Finset A) (by simpa only [card_univ,Fintype.card_coe] using va)
    (by simpa only [Fintype.card_coe] using pa) keptLength keptDegree keptUpper
  simp only [card_univ,Fintype.card_coe]
  change (M:ℝ)/retention ≤ ((∑ v : A, (occurrences (fun i => (kept i).toFinset) v).card : ℕ):ℝ) -
    (M:ℝ)/(4*(n:ℝ))*A.card - (M:ℝ)/(4*(p:ℝ))*B.card
  rw [counted]
  linarith only [enough]

end OnlineReachabilityPreservers
