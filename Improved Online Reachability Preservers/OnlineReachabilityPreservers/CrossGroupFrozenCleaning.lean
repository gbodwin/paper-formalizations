import OnlineReachabilityPreservers.CrossGroupOppositeLinks
import OnlineReachabilityPreservers.FrozenDistinctCleaning
import OnlineReachabilityPreservers.FrozenMatchedPartners

/-! Frozen half-five cleaning when original cross-group links are sparse. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

/-- At high mass, charge trimming and pruning to the vertex budget and the
original cross-group opposite links. Low mass needs no link bound. -/
theorem regularization_list_frozen_half_five_of_cross_group_links {n p : ℕ}
    (rows : Fin p → List (Fin n)) (simple : ∀ i, (rows i).Nodup)
    (free : HalfBridgeFree (Before rows) 5) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (rows i).length) (long : p ≤ ∑ i, (rows i).length)
    (first : Fin n → Fin p) (firstSpec : ∀ i, ∀ v ∈ rows i, v ∈ rows (first v) ∧ first v ≤ i)
    (budget : let two : HalfBridgeFree (Before rows) 2 := fun _ size => free (size.trans (by decide))
      8 * max n p < (∑ i, (rows i).length) →
      24 * (n + Nat.card (crossGroupOppositeLinkGraph rows two first).edgeSet) ≤
        11 * (∑ i, (rows i).length)) :
    let M := ∑ i, (rows i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (Before clean) 5 ∧
      M ≤ 288 * (∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (rows i).length
  by_cases low : M ≤ 8 * max n p
  · obtain ⟨n',vertices,p',paths,clean,cleanSimple,cleanFree,lower,upper,caps⟩ :=
      regularization_list_frozen_low_mass_at_cutoff 5 rows simple free (by decide) hn hp dense long low
    exact ⟨n',vertices,p',paths,clean,cleanSimple,cleanFree.halfFree,by omega,upper,caps⟩
  have paid := budget (lt_of_not_ge low)
  obtain ⟨kept,sub,_,_,unique,loss⟩ :=
    free.exists_unique_intersections_with_cross_group_link_bound (by decide) simple hp first firstSpec
  exact regularization_list_frozen_half_five_of_large_unique_sublists rows kept simple free sub
    (fun {_ _ _ _} => unique) hn hp dense long (by omega)

/-- The cross-group link budget also yields a witness with distinct,
nonempty paths for feasible literal inputs. -/
theorem regularization_list_frozen_half_five_distinct_of_cross_group_links {n p : ℕ}
    (rows : Fin p → List (Fin n)) (distinct : Function.Injective rows) (nonempty : ∀ i, rows i ≠ [])
    (simple : ∀ i, (rows i).Nodup) (free : HalfBridgeFree (Before rows) 5)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (rows i).length)
    (first : Fin n → Fin p) (firstSpec : ∀ i, ∀ v ∈ rows i, v ∈ rows (first v) ∧ first v ≤ i)
    (budget : let two : HalfBridgeFree (Before rows) 2 := fun _ size => free (size.trans (by decide))
      8 * max n p < (∑ i, (rows i).length) →
      24 * (n + Nat.card (crossGroupOppositeLinkGraph rows two first).edgeSet) ≤
        11 * (∑ i, (rows i).length)) :
    let M := ∑ i, (rows i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      Function.Injective clean ∧ (∀ i, clean i ≠ []) ∧ (∀ i, (clean i).Nodup) ∧
      HalfBridgeFree (Before clean) 5 ∧ M ≤ 288 * (∑ i, (clean i).length) ∧
      (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  regularization_list_frozen_distinct_of_indexed (half := true) (k := 5) (retention := 288)
    rows distinct nonempty simple free (by decide) hn hp dense (by decide)
    (fun long => regularization_list_frozen_half_five_of_cross_group_links rows simple free
      hn hp dense long first firstSpec budget)

end OnlineReachabilityPreservers
