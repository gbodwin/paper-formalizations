import OnlineReachabilityPreservers.ShortReturnExcessRefinement

/-! Clip recomputed components while retaining the original averages. -/

namespace OnlineReachabilityPreservers

open Finset

/-- Charge degree clipping and then path clipping on the resulting rows. -/
def shortReturnSuccessiveExcess {I V : Type*} [LinearOrder I] [LinearOrder V] [Fintype I] [Fintype V]
    (rows : I → List V) (D L k : ℕ) : ℕ :=
  shortReturnDegreeExcessMass rows D k +
    shortReturnPathExcessMass (clipShortReturnDegreeComponents rows D k) L k

/-- An arbitrary rowwise restriction may be followed by both component
clips at the original widths. If the initial deletions and both clips
lose at most a third of the original mass, frozen cleaning keeps at
least one eighteenth. -/
theorem regularization_list_frozen_of_small_successive_excess_after_sublist {n p k : ℕ} {half : Bool}
    (rows kept : Fin p → List (Fin n)) (simple : ∀ i, (rows i).Nodup)
    (free : localOrderAdmissible half k rows) (sub : ∀ i, (kept i).Sublist (rows i))
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (rows i).length) (long : p ≤ ∑ i, (rows i).length)
    (excess : let M := ∑ i, (rows i).length
      3*(M - (∑ i, (kept i).length) + shortReturnSuccessiveExcess kept (4*M/n) (4*M/p) k) ≤ M) :
    let M := ∑ i, (rows i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 18*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧
      frozenListCaps n p M clean := by
  let M := ∑ i, (rows i).length
  let K := ∑ i, (kept i).length
  let D := 4*M/n
  let L := 4*M/p
  let degreeKept := clipShortReturnDegreeComponents kept D k
  let clipped := clipShortReturnPathComponents degreeKept L k
  have keptSimple (i : Fin p) : (kept i).Nodup := (sub i).nodup (simple i)
  have keptUpper : K ≤ M := sum_le_sum (fun i _ => (sub i).length_le)
  obtain ⟨clipSub, degree, path, paid⟩ := clipShortReturnComponents_spec kept keptSimple D L k
  change (∑ i, (clipped i).length) + shortReturnSuccessiveExcess kept D L k = K at paid
  change 3*(M-K + shortReturnSuccessiveExcess kept D L k) ≤ M at excess
  exact regularization_list_frozen_of_short_return_restriction rows simple free hn hp dense long clipped
    (fun i => (clipSub i).trans (sub i)) degree path (by omega)

/-- Both excesses can also be checked directly on the first restriction.
The degree clip cannot enlarge the recomputed path excess. -/
theorem regularization_list_frozen_of_small_recomputed_excess_after_sublist {n p k : ℕ} {half : Bool}
    (rows kept : Fin p → List (Fin n)) (simple : ∀ i, (rows i).Nodup)
    (free : localOrderAdmissible half k rows) (sub : ∀ i, (kept i).Sublist (rows i))
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (rows i).length) (long : p ≤ ∑ i, (rows i).length)
    (excess : let M := ∑ i, (rows i).length
      3*(M - (∑ i, (kept i).length) + shortReturnDegreeExcessMass kept (4*M/n) k +
        shortReturnPathExcessMass kept (4*M/p) k) ≤ M) :
    let M := ∑ i, (rows i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 18*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧
      frozenListCaps n p M clean := by
  let M := ∑ i, (rows i).length
  let D := 4*M/n
  let L := 4*M/p
  have keptSimple (i : Fin p) : (kept i).Nodup := (sub i).nodup (simple i)
  have degreeSub (i : Fin p) : (clipShortReturnDegreeComponents kept D k i).Sublist (kept i) :=
    List.filter_sublist
  have pathLoss := (shortReturnExcess_le_of_sublist keptSimple degreeSub D L k).2
  refine regularization_list_frozen_of_small_successive_excess_after_sublist rows kept simple free sub
    hn hp dense long ?_
  change 3*(M - (∑ i, (kept i).length) + shortReturnSuccessiveExcess kept D L k) ≤ M
  change 3*(M - (∑ i, (kept i).length) + shortReturnDegreeExcessMass kept D k +
      shortReturnPathExcessMass kept L k) ≤ M at excess
  unfold shortReturnSuccessiveExcess
  omega

/-- Feasible distinct nonempty inputs give a literal distinct nonempty
witness under the successive excess test at every cutoff of at least two. -/
theorem regularization_list_frozen_distinct_of_small_successive_excess_after_sublist {n p k : ℕ} {half : Bool}
    (rows kept : Fin p → List (Fin n))
    (distinct : Function.Injective rows) (nonempty : ∀ i, rows i ≠ [])
    (simple : ∀ i, (rows i).Nodup) (sub : ∀ i, (kept i).Sublist (rows i))
    (free : localOrderAdmissible half k rows) (two : 2 ≤ k)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (rows i).length)
    (excess : let M := ∑ i, (rows i).length
      3*(M - (∑ i, (kept i).length) + shortReturnSuccessiveExcess kept (4*M/n) (4*M/p) k) ≤ M) :
    let M := ∑ i, (rows i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      Function.Injective clean ∧ (∀ i, clean i ≠ []) ∧ (∀ i, (clean i).Nodup) ∧
      localOrderAdmissible half k clean ∧ M ≤ 18*(∑ i, (clean i).length) ∧
      (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  refine regularization_list_frozen_distinct_of_indexed (retention := 18) rows distinct nonempty simple
    free two hn hp dense (by decide) ?_
  dsimp only
  exact fun long => regularization_list_frozen_of_small_successive_excess_after_sublist rows kept simple free sub
    hn hp dense long excess

end OnlineReachabilityPreservers
