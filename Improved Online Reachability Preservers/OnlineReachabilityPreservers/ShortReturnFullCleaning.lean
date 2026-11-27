import OnlineReachabilityPreservers.ShortReturnStandardCleaning

/-! Full-mode cleaning uses ordinary degree copies at every cutoff. -/

namespace OnlineReachabilityPreservers

local notation "Before" => SourceAudit.BeforeIn

/-- In full mode the original path-component test suffices on its own.
Standard degree copying always preserves full exclusion. -/
theorem regularization_list_frozen_full_of_original_path_component_room {n p k : ℕ}
    (rows : Fin p → List (Fin n)) (simple : ∀ i, (rows i).Nodup)
    (free : BridgeFree (Before rows) k)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (rows i).length) (long : p ≤ ∑ i, (rows i).length)
    (pathRoom : let M := ∑ i, (rows i).length
      ∀ i, ∀ x ∈ rows i, (shortReturnRowComponent rows k i x).card ≤ 4*M/p) :
    let M := ∑ i, (rows i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) k ∧
      M ≤ 4*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧
      frozenListCaps n p M clean :=
  regularization_list_frozen_of_original_path_component_room (half := false)
    rows simple free hn hp dense long (fun impossible => by cases impossible) pathRoom

/-- In full mode a restriction retaining two thirds of the mass needs
only the path-component criterion. Standard degree splitting supplies
the capped degree profile and preserves the full cutoff. -/
theorem regularization_list_frozen_full_of_short_return_path_restriction {n p k : ℕ}
    (rows : Fin p → List (Fin n)) (simple : ∀ i, (rows i).Nodup)
    (free : BridgeFree (Before rows) k)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (rows i).length) (long : p ≤ ∑ i, (rows i).length)
    (kept : Fin p → List (Fin n)) (sub : ∀ i, (kept i).Sublist (rows i))
    (pathRoom : let M := ∑ i, (rows i).length
      ∀ i, ∀ v ∈ kept i, (shortReturnRowComponent kept k i v).card ≤ 4*M/p)
    (roomMass : 2*(∑ i, (rows i).length) ≤ 3*(∑ i, (kept i).length)) :
    let M := ∑ i, (rows i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) k ∧
      M ≤ 18*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧
      frozenListCaps n p M clean :=
  regularization_list_frozen_of_short_return_path_restriction (half := false)
    rows simple free hn hp dense long
    kept sub (fun impossible => by cases impossible) pathRoom roomMass

/-- In full mode the original path excess alone can supply a
two-thirds restriction. Standard degree copying follows the restriction. -/
theorem regularization_list_frozen_full_of_small_short_return_path_excess {n p k : ℕ}
    (rows : Fin p → List (Fin n)) (simple : ∀ i, (rows i).Nodup)
    (free : BridgeFree (Before rows) k)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (rows i).length) (long : p ≤ ∑ i, (rows i).length)
    (excess : let M := ∑ i, (rows i).length; 3*shortReturnPathExcessMass rows (4*M/p) k ≤ M) :
    let M := ∑ i, (rows i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) k ∧
      M ≤ 18*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧
      frozenListCaps n p M clean :=
  regularization_list_frozen_of_small_short_return_path_excess (half := false)
    rows simple free hn hp dense long (fun impossible => by cases impossible) excess

/-- The full-mode path-excess condition also gives a literal distinct
nonempty witness at every cutoff of at least two. -/
theorem regularization_list_frozen_full_distinct_of_small_short_return_path_excess {n p k : ℕ}
    (rows : Fin p → List (Fin n)) (distinct : Function.Injective rows)
    (nonempty : ∀ i, rows i ≠ []) (simple : ∀ i, (rows i).Nodup)
    (free : BridgeFree (Before rows) k) (two : 2 ≤ k)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (rows i).length)
    (excess : let M := ∑ i, (rows i).length; 3*shortReturnPathExcessMass rows (4*M/p) k ≤ M) :
    let M := ∑ i, (rows i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      Function.Injective clean ∧ (∀ i, clean i ≠ []) ∧ (∀ i, (clean i).Nodup) ∧
      BridgeFree (Before clean) k ∧ M ≤ 18*(∑ i, (clean i).length) ∧
      (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  regularization_list_frozen_distinct_of_small_short_return_path_excess (half := false)
    rows distinct nonempty simple free two hn hp dense (fun impossible => by cases impossible) excess

end OnlineReachabilityPreservers
