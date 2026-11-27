import OnlineReachabilityPreservers.FullReturnRadius
import OnlineReachabilityPreservers.ShortReturnStandardCleaning

/-! Group the short returns at the sufficient radius for each full cutoff. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped Sigma.Lex
local notation "Before" => SourceAudit.BeforeIn

/-- Pack groups at radius cutoff minus five using the original
width and preserving full exclusion at the original cutoff. -/
theorem split_of_capped_full_return_partition {V : Type*} [LinearOrder V] [Fintype V]
    {p w cutoff : ℕ} {rows : Fin p → List V} (simple : ∀ i, (rows i).Nodup)
    (free : BridgeFree (Before rows) cutoff) (large : 7 ≤ cutoff)
    (canGroup : HasCappedShortReturnPartition rows w (cutoff-2)) :
    ∃ (sizes : Fin p → ℕ) (pieces : (Σₗ i : Fin p, Fin (sizes i)) → List V),
      (∀ i, (pieces i).Nodup) ∧ BridgeFree (Before pieces) cutoff ∧
      (∀ i, (pieces i).length ≤ w) ∧
      (∑ i, (pieces i).length) = ∑ i, (rows i).length ∧
      (∀ x, (occurrences (fun i => (pieces i).toFinset) x).card =
        (occurrences (fun i => (rows i).toFinset) x).card) ∧
      ({i ∈ univ | (pieces i).length ≤ w/2} : Finset (Σₗ i : Fin p, Fin (sizes i))).card ≤ p := by
  let G := listPiecePrecedenceGraph rows
  let linked (i : Fin p) (x y : V) := Before rows i x y ∧ y ∈ reachIn G x (cutoff-2-3)
  refine split_of_capped_path_partitions (half := false) (cutoff := cutoff) simple linked canGroup ?_
  intro sizes pieces step disjoint together
  let J := Σₗ i : Fin p, Fin (sizes i)
  refine bridgeFree_of_disjoint_split_of_short_parent_returns G id (fun j : J => j.fst)
    @step (fun {j _ _} before => listPiecePrecedenceGraph_edge.mpr ⟨j.fst, step before⟩)
    @disjoint ?_ free large
  intro i j x y apart parent left right before back
  have radius : cutoff-2-3 = cutoff-5 := by omega
  exact apart (together parent left right ⟨before, by simpa only [radius, id_eq] using back⟩)

/-- The grouped standard degree copies give a frozen quarter-mass
witness at any full cutoff of at least seven. -/
theorem regularization_list_frozen_full_of_copied_short_return_components {n p cutoff : ℕ}
    (rows : Fin p → List (Fin n)) (simple : ∀ i, (rows i).Nodup)
    (free : BridgeFree (Before rows) cutoff) (large : 7 ≤ cutoff)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (rows i).length) (long : p ≤ ∑ i, (rows i).length)
    (room : let M := ∑ i, (rows i).length; let copies := splitListVertices rows (4*M/n)
      ∀ i, ∀ x ∈ copies i, (shortReturnRowComponent copies (cutoff-2) i x).card ≤ 4*M/p) :
    let M := ∑ i, (rows i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) cutoff ∧
      M ≤ 4*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (rows i).length
  let D := 4*M/n
  let copies := splitListVertices rows D
  have copied : BridgeFree (Before copies) cutoff :=
    free.split_list_vertices_any (·.fst) (fun {i _ _} => splitListVertices_step (simple i))
  have copySimple (i : Fin p) : (copies i).Nodup := splitListVertices_simple rows D i (simple i)
  have packed := split_of_capped_full_return_partition copySimple copied large
    ((hasCappedShortReturnPartition_iff_component_room copies _ _).mpr room)
  exact regularization_list_frozen_after_packing_standard_degree_copies (half := false) (k := cutoff)
    rows hn hp dense long packed

/-- The same component-width premise may be tested on the original rows. -/
theorem regularization_list_frozen_full_of_short_return_components {n p cutoff : ℕ}
    (rows : Fin p → List (Fin n)) (simple : ∀ i, (rows i).Nodup)
    (free : BridgeFree (Before rows) cutoff) (large : 7 ≤ cutoff)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (rows i).length) (long : p ≤ ∑ i, (rows i).length)
    (room : let M := ∑ i, (rows i).length
      ∀ i, ∀ x ∈ rows i, (shortReturnRowComponent rows (cutoff-2) i x).card ≤ 4*M/p) :
    let M := ∑ i, (rows i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) cutoff ∧
      M ≤ 4*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  exact regularization_list_frozen_full_of_copied_short_return_components rows simple free large hn hp
    dense long (splitListVertices_short_return_path_room simple room)

/-- Feasible distinct nonempty input gives an eighth of the original
mass under the same shortened original-group test. -/
theorem regularization_list_frozen_full_distinct_of_short_return_components {n p cutoff : ℕ}
    (rows : Fin p → List (Fin n)) (distinct : Function.Injective rows)
    (nonempty : ∀ i, rows i ≠ []) (simple : ∀ i, (rows i).Nodup)
    (free : BridgeFree (Before rows) cutoff) (large : 7 ≤ cutoff)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (rows i).length)
    (room : let M := ∑ i, (rows i).length
      ∀ i, ∀ x ∈ rows i, (shortReturnRowComponent rows (cutoff-2) i x).card ≤ 4*M/p) :
    let M := ∑ i, (rows i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      Function.Injective clean ∧ (∀ i, clean i ≠ []) ∧ (∀ i, (clean i).Nodup) ∧
      BridgeFree (Before clean) cutoff ∧ M ≤ 8*(∑ i, (clean i).length) ∧
      (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  refine regularization_list_frozen_distinct_of_indexed (half := false) (k := cutoff) (retention := 8)
    rows distinct nonempty simple free (by omega) hn hp dense (by decide) ?_
  dsimp only
  intro long
  obtain ⟨n', vertices, p', paths, clean, cleanSimple, allowed, lower, upper, caps⟩ :=
    regularization_list_frozen_full_of_short_return_components rows simple free large hn hp dense long room
  exact ⟨n', vertices, p', paths, clean, cleanSimple, allowed, by omega, upper, caps⟩

end OnlineReachabilityPreservers
