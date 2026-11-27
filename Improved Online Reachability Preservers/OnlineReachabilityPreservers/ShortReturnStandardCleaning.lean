import OnlineReachabilityPreservers.ShortReturnComponentClipping

/-! Path-component cleaning when standard degree splits preserve the selected bridge exclusion. -/

namespace OnlineReachabilityPreservers

open Finset

/-- The same width and cutoff satisfy the degree-splitting criterion after
taking rowwise sublists. -/
theorem HalfDegreeSplitCondition.of_sublist {n p D k : ℕ} {rows kept : Fin p → List (Fin n)}
    (safe : HalfDegreeSplitCondition rows D k)
    (simple : ∀ i, (rows i).Nodup) (sub : ∀ i, (kept i).Sublist (rows i)) :
    HalfDegreeSplitCondition kept D k := by
  rcases safe with noCycles | short | full | degree
  · left
    intro x y edge back
    have lifts {a b : Fin n} (step : Edge (pathPrecedenceGraph kept) a b) :
        Edge (pathPrecedenceGraph rows) a b := by
      simp only [Edge, pathPrecedenceGraph, mem_filter, mem_univ, true_and] at step ⊢
      obtain ⟨i, ordered⟩ := step
      exact ⟨i, listBefore_of_sublist (simple i) (sub i) ordered⟩
    exact noCycles (lifts edge) (project_reachIn id (fun {_ _} step => lifts step) _ back)
  · exact Or.inr (Or.inl short)
  · exact Or.inr (Or.inr (Or.inl (localOrderAdmissible_of_sublist (half := false) simple sub full)))
  · right
    right
    right
    intro v
    refine (card_le_card ?_).trans (degree v)
    intro i present
    simp only [mem_occurrences, List.mem_toFinset] at present ⊢
    exact (sub i).subset present

/-- The original path-component width also bounds the components
of every copied row after ordinary degree splitting. -/
private theorem splitListVertices_short_return_path_room {n p k D L : ℕ}
    {rows : Fin p → List (Fin n)} (simple : ∀ i, (rows i).Nodup)
    (room : ∀ i, ∀ x ∈ rows i, (shortReturnRowComponent rows k i x).card ≤ L) :
    ∀ i, ∀ v ∈ splitListVertices rows D i,
      (shortReturnRowComponent (splitListVertices rows D) k i v).card ≤ L := by
  intro i v on
  let project (x : ListVertexBlockIndex rows D) := x.fst
  have projects (j : Fin p) : (splitListVertices rows D j).map project = rows j :=
    splitListVertices_project rows D j
  have projected := List.mem_map_of_mem (f := project) on
  rw [projects i] at projected
  exact (shortReturnRowComponent_card_le_project project simple projects k i v).trans (room i _ projected)

/-- The original path-component bound gives a frozen quarter-mass witness
whenever standard degree copying is safe. -/
theorem regularization_list_frozen_of_original_path_component_room {n p k : ℕ} {half : Bool}
    (rows : Fin p → List (Fin n)) (simple : ∀ i, (rows i).Nodup)
    (free : localOrderAdmissible half k rows)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (rows i).length) (long : p ≤ ∑ i, (rows i).length)
    (halfSafe : half = true → HalfDegreeSplitCondition rows (4*(∑ i, (rows i).length)/n) k)
    (pathRoom : let M := ∑ i, (rows i).length
      ∀ i, ∀ x ∈ rows i, (shortReturnRowComponent rows k i x).card ≤ 4*M/p) :
    let M := ∑ i, (rows i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 4*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧
      frozenListCaps n p M clean := by
  exact regularization_list_frozen_of_short_return_component_room
    rows simple hn hp dense long
    (splitListVertices_admissible_of_halfDegreeSplitCondition rows simple free halfSafe)
    (splitListVertices_short_return_path_room simple pathRoom)

/-- Standard degree copies with the chosen exclusion give a frozen
witness when the retained sublists pass the original path-width test
and keep at least two thirds of the original mass. -/
private theorem frozen_of_standard_copy_restriction {n p k : ℕ} {half : Bool}
    (rows : Fin p → List (Fin n)) (simple : ∀ i, (rows i).Nodup)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (rows i).length) (long : p ≤ ∑ i, (rows i).length)
    (kept : Fin p → List (Fin n)) (sub : ∀ i, (kept i).Sublist (rows i))
    (copyLegal : let M := ∑ i, (rows i).length
      localOrderAdmissible half k (splitListVertices kept (4*M/n)))
    (pathRoom : let M := ∑ i, (rows i).length
      ∀ i, ∀ v ∈ kept i, (shortReturnRowComponent kept k i v).card ≤ 4*M/p)
    (roomMass : 2*(∑ i, (rows i).length) ≤ 3*(∑ i, (kept i).length)) :
    let M := ∑ i, (rows i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 18*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧
      frozenListCaps n p M clean := by
  let M := ∑ i, (rows i).length
  let D := 4*M/n
  let L := 4*M/p
  let K := ∑ i, (kept i).length
  let copies := splitListVertices kept D
  let V := ListVertexBlockIndex kept D
  have dPos : 0 < D := (four_average_width hn dense).1
  have keptSimple (i : Fin p) : (kept i).Nodup := (sub i).nodup (simple i)
  have room : HasCappedShortReturnPartition copies L k :=
    (hasCappedShortReturnPartition_iff_component_room _ _ _).mpr
      (splitListVertices_short_return_path_room keptSimple pathRoom)
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
  refine regularization_list_frozen_after_grouped_width_splits_of_mass copies
    (fun i => splitListVertices_simple kept D i (keptSimple i)) copyLegal hn hp dense long
    (copyMass.trans_le upper) degree light room ?_
  dsimp only
  rw [copyMass]
  exact fun _ _ _ paid lossV lossI =>
    shortReturnTrim_mass_of_two_thirds hn hp (hn.trans_le dense) roomMass upper paid lossV lossI

/-- A restriction retaining two thirds of the mass only needs the path
components to fit when its standard degree split is safe. The original
widths are used throughout. -/
theorem regularization_list_frozen_of_short_return_path_restriction {n p k : ℕ} {half : Bool}
    (rows : Fin p → List (Fin n)) (simple : ∀ i, (rows i).Nodup)
    (free : localOrderAdmissible half k rows)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (rows i).length) (long : p ≤ ∑ i, (rows i).length)
    (kept : Fin p → List (Fin n)) (sub : ∀ i, (kept i).Sublist (rows i))
    (halfSafe : half = true → HalfDegreeSplitCondition kept (4*(∑ i, (rows i).length)/n) k)
    (pathRoom : let M := ∑ i, (rows i).length
      ∀ i, ∀ v ∈ kept i, (shortReturnRowComponent kept k i v).card ≤ 4*M/p)
    (roomMass : 2*(∑ i, (rows i).length) ≤ 3*(∑ i, (kept i).length)) :
    let M := ∑ i, (rows i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 18*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧
      frozenListCaps n p M clean := by
  have keptSimple (i : Fin p) : (kept i).Nodup := (sub i).nodup (simple i)
  have retained := localOrderAdmissible_of_sublist simple sub free
  exact frozen_of_standard_copy_restriction rows simple hn hp dense long kept sub
    (splitListVertices_admissible_of_halfDegreeSplitCondition kept keptSimple retained halfSafe) pathRoom roomMass

/-- Path-component excess alone supplies a two-thirds restriction under
the stated condition for safe standard degree copying. -/
theorem regularization_list_frozen_of_small_short_return_path_excess {n p k : ℕ} {half : Bool}
    (rows : Fin p → List (Fin n)) (simple : ∀ i, (rows i).Nodup)
    (free : localOrderAdmissible half k rows)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (rows i).length) (long : p ≤ ∑ i, (rows i).length)
    (halfSafe : half = true → HalfDegreeSplitCondition rows (4*(∑ i, (rows i).length)/n) k)
    (excess : let M := ∑ i, (rows i).length; 3*shortReturnPathExcessMass rows (4*M/p) k ≤ M) :
    let M := ∑ i, (rows i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 18*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧
      frozenListCaps n p M clean := by
  let M := ∑ i, (rows i).length
  let L := 4*M/p
  let kept := clipShortReturnPathComponents rows L k
  have total : (∑ i, (kept i).length) + shortReturnPathExcessMass rows L k = M :=
    clipShortReturnPathComponents_mass rows simple L k
  change 3*shortReturnPathExcessMass rows L k ≤ M at excess
  have sub := clipShortReturnPathComponents_sublist rows L k
  exact regularization_list_frozen_of_short_return_path_restriction rows simple free hn hp dense long
    kept sub (fun mode => (halfSafe mode).of_sublist simple sub)
    (clipShortReturnPathComponents_room rows simple L k) (by omega)

/-- The same condition gives a literal distinct nonempty witness at every
cutoff of at least two. -/
theorem regularization_list_frozen_distinct_of_small_short_return_path_excess {n p k : ℕ} {half : Bool}
    (rows : Fin p → List (Fin n)) (distinct : Function.Injective rows)
    (nonempty : ∀ i, rows i ≠ []) (simple : ∀ i, (rows i).Nodup)
    (free : localOrderAdmissible half k rows) (two : 2 ≤ k)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (rows i).length)
    (halfSafe : half = true → HalfDegreeSplitCondition rows (4*(∑ i, (rows i).length)/n) k)
    (excess : let M := ∑ i, (rows i).length; 3*shortReturnPathExcessMass rows (4*M/p) k ≤ M) :
    let M := ∑ i, (rows i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      Function.Injective clean ∧ (∀ i, clean i ≠ []) ∧ (∀ i, (clean i).Nodup) ∧
      localOrderAdmissible half k clean ∧ M ≤ 18*(∑ i, (clean i).length) ∧
      (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  refine regularization_list_frozen_distinct_of_indexed (retention := 18) rows distinct nonempty simple
    free two hn hp dense (by decide) ?_
  dsimp only
  exact fun long => regularization_list_frozen_of_small_short_return_path_excess rows simple free
    hn hp dense long halfSafe excess

end OnlineReachabilityPreservers
