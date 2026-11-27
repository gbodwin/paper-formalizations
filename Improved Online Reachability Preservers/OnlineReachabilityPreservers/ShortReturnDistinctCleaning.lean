import OnlineReachabilityPreservers.FrozenDistinctCleaning
import OnlineReachabilityPreservers.ShortReturnVertexPacking

/-! Transfer the two grouped-width tests to literal sets of simple paths. -/

namespace OnlineReachabilityPreservers

/-- For literal inputs and a cutoff of at least two, the two original
component tests give a frozen witness of distinct nonempty paths. -/
theorem regularization_list_frozen_distinct_of_short_return_component_rooms {n p k : ℕ} {half : Bool}
    (rows : Fin p → List (Fin n)) (distinct : Function.Injective rows)
    (nonempty : ∀ i, rows i ≠ []) (simple : ∀ i, (rows i).Nodup)
    (free : localOrderAdmissible half k rows) (two : 2 ≤ k)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (rows i).length)
    (degreeRoom : let M := ∑ i, (rows i).length
      ∀ v i, v ∈ rows i → (shortReturnCopyRowComponent rows k v i).card ≤ 4*M/n)
    (pathRoom : let M := ∑ i, (rows i).length
      ∀ i, ∀ x ∈ rows i, (shortReturnRowComponent rows k i x).card ≤ 4*M/p) :
    let M := ∑ i, (rows i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      Function.Injective clean ∧ (∀ i, clean i ≠ []) ∧ (∀ i, (clean i).Nodup) ∧
      localOrderAdmissible half k clean ∧ M ≤ 8*(∑ i, (clean i).length) ∧
      (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  refine regularization_list_frozen_distinct_of_indexed rows distinct nonempty simple
    free two hn hp dense (by decide) ?_
  dsimp only
  intro long
  obtain ⟨n', nCap, p', pCap, clean, cleanSimple, cleanFree, mass, upper, caps⟩ :=
    regularization_list_frozen_of_short_return_component_rooms rows simple free hn hp dense long degreeRoom pathRoom
  exact ⟨n', nCap, p', pCap, clean, cleanSimple, cleanFree, by omega, upper, caps⟩

end OnlineReachabilityPreservers
