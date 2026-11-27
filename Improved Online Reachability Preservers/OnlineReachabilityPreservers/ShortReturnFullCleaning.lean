import OnlineReachabilityPreservers.ShortReturnComponentClipping

/-! Full-mode cleaning uses ordinary degree copies at every cutoff. -/

namespace OnlineReachabilityPreservers

open Finset
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
      frozenListCaps n p M clean := by
  let M := ∑ i, (rows i).length
  let D := 4*M/n
  let copies := splitListVertices rows D
  let project (v : ListVertexBlockIndex rows D) := v.fst
  have projects (i : Fin p) : (copies i).map project = rows i := splitListVertices_project rows D i
  have legal : BridgeFree (Before copies) k :=
    free.split_list_vertices_any project (fun {i _ _} step => splitListVertices_step (simple i) step)
  have room (i : Fin p) (v : ListVertexBlockIndex rows D) (on : v ∈ copies i) :
      (shortReturnRowComponent copies k i v).card ≤ 4*M/p := by
    have projected := List.mem_map_of_mem (f := project) on
    rw [projects i] at projected
    exact (shortReturnRowComponent_card_le_project project simple projects k i v).trans (pathRoom i _ projected)
  exact regularization_list_frozen_of_short_return_component_room (half := false)
    rows simple hn hp dense long legal room

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
      frozenListCaps n p M clean := by
  let M := ∑ i, (rows i).length
  let D := 4*M/n
  let L := 4*M/p
  let K := ∑ i, (kept i).length
  let copies := splitListVertices kept D
  let V := ListVertexBlockIndex kept D
  let project (v : V) := v.fst
  have dPos : 0 < D := (four_average_width hn dense).1
  have keptSimple (i : Fin p) : (kept i).Nodup := (sub i).nodup (simple i)
  have retained : BridgeFree (Before kept) k := localOrderAdmissible_of_sublist (half := false) simple sub free
  have projects (i : Fin p) : (copies i).map project = kept i := splitListVertices_project kept D i
  have legal : BridgeFree (Before copies) k :=
    retained.split_list_vertices_any project (fun {i _ _} step => splitListVertices_step (keptSimple i) step)
  have room : HasCappedShortReturnPartition copies L k := by
    apply (hasCappedShortReturnPartition_iff_component_room _ _ _).mpr
    intro i v on
    have projected := List.mem_map_of_mem (f := project) on
    rw [projects i] at projected
    exact (shortReturnRowComponent_card_le_project project keptSimple projects k i v).trans (pathRoom i _ projected)
  have upper : K ≤ M := sum_le_sum (fun i _ => (sub i).length_le)
  have copyMass : (∑ i, (copies i).length) = K := by simp [copies, K]
  let marks := fun i => (copies i).toFinset
  have degree (v : V) : (occurrences marks v).card ≤ D := by
    have same : marks = splitVertices (fun i => (kept i).toFinset) D :=
      funext (splitListVertices_toFinset kept D)
    rw [same]
    exact splitVertices_degree (fun i => (kept i).toFinset) dPos v
  obtain ⟨full, filled, remainders⟩ := splitListVertices_full_block_profile kept dPos
  have light : ({v ∈ univ | (occurrences marks v).card ≤ D/2} : Finset V).card ≤ n := by
    refine (card_le_card ?_).trans (remainders.le.trans_eq (Fintype.card_fin n))
    intro v on
    refine mem_sdiff.mpr ⟨mem_univ _, fun onFull => ?_⟩
    have small := (mem_filter.mp on).2
    have exactDegree : (occurrences marks v).card = D := filled v onFull
    rw [exactDegree] at small
    exact (Nat.div_lt_self dPos (by decide : 1 < 2)).not_ge small
  refine regularization_list_frozen_after_grouped_width_splits_of_mass (half := false) copies
    (fun i => splitListVertices_simple kept D i (keptSimple i)) legal hn hp dense long
    (copyMass.trans_le upper) degree light room ?_
  dsimp only
  rw [copyMass]
  exact fun _ _ _ paid lossV lossI =>
    shortReturnTrim_mass_of_two_thirds hn hp (hn.trans_le dense) roomMass upper paid lossV lossI

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
      frozenListCaps n p M clean := by
  let M := ∑ i, (rows i).length
  let L := 4*M/p
  let kept := clipShortReturnPathComponents rows L k
  have total : (∑ i, (kept i).length) + shortReturnPathExcessMass rows L k = M :=
    clipShortReturnPathComponents_mass rows simple L k
  change 3*shortReturnPathExcessMass rows L k ≤ M at excess
  exact regularization_list_frozen_full_of_short_return_path_restriction rows simple free hn hp dense long
    kept (clipShortReturnPathComponents_sublist rows L k) (clipShortReturnPathComponents_room rows simple L k) (by omega)

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
      (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  refine regularization_list_frozen_distinct_of_indexed (half := false) rows distinct nonempty simple
    free two hn hp dense (by decide) ?_
  dsimp only
  exact fun long => regularization_list_frozen_full_of_small_short_return_path_excess rows simple free
    hn hp dense long excess

end OnlineReachabilityPreservers
