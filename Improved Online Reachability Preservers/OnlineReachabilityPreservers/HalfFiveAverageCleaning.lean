import OnlineReachabilityPreservers.HalfFiveProjection

/-! Half-five cleaning relative to the output averages. -/

namespace OnlineReachabilityPreservers

local notation "ListBefore" => SourceAudit.BeforeIn

/-- Half exclusion through size five admits a constant-mass witness
within both original budgets and all four output-average caps. -/
theorem regularization_list_output_average_half_five {n p : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (allowed : HalfBridgeFree (ListBefore paths) 5)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (ListBefore clean) 5 ∧
      (∑ i, (paths i).length) ≤ 392*(∑ i, (clean i).length) ∧
      (∑ i, (clean i).length) ≤ (∑ i, (paths i).length) ∧ listOutputAverageCaps clean :=
  regularization_list_output_average_of_pruned_rectangle_splits paths simple true allowed
    (by decide) (fun _ _ D L simple unique allowed =>
      listRegularizedPaths_halfFree_five_of_unique_intersections simple allowed (fun {_ _ _ _} => unique) D L)
    hn hp dense long

/-- At the unrestricted half-five maximum, retain at least one 392nd of the
mass with both original budgets and the witness's own average caps. -/
theorem localOrderExtremal_output_average_half_five (n p : ℕ) (hn : 0 < n) (hp : 0 < p) :
    ∃ paths : Fin p → List (Fin n), (∀ i, (paths i).Nodup) ∧ HalfBridgeFree (ListBefore paths) 5 ∧
      (∀ other : Fin p → List (Fin n), (∀ i, (other i).Nodup) → HalfBridgeFree (ListBefore other) 5 →
        (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
      ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
        (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (ListBefore clean) 5 ∧
        (∑ i, (paths i).length) ≤ 392*(∑ i, (clean i).length) ∧
        (∑ i, (clean i).length) ≤ (∑ i, (paths i).length) ∧ listOutputAverageCaps clean := by
  obtain ⟨paths,simple,allowed,maximal,dense,long⟩ := localOrderExtremal_isDense n p 5 true hn hp
  exact ⟨paths,simple,allowed,maximal,
    regularization_list_output_average_half_five paths simple allowed hn hp dense long⟩

end OnlineReachabilityPreservers
