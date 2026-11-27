import OnlineReachabilityPreservers.FrozenDistinctCleaning
import OnlineReachabilityPreservers.ShortReturnOverflow

/-! Clip degree components and then path components. -/

namespace OnlineReachabilityPreservers

open Finset

variable {I V : Type*} [Fintype I] [Fintype V] [LinearOrder I] [LinearOrder V]

private def degreeComponentSelection (rows : I → List V) (width cutoff : ℕ) (v : V) : Finset I :=
  selectLinkedGroups (occurrences (fun j => (rows j).toFinset) v)
    (shortReturnCopyRowGraph rows cutoff v) width

private def pathComponentSelection (rows : I → List V) (width cutoff : ℕ) (i : I) : Finset V :=
  selectLinkedGroups (rows i).toFinset (shortReturnRowGraph rows cutoff i) width

/-- Keep the selected incident row labels within each degree component. -/
def clipShortReturnDegreeComponents (rows : I → List V) (width cutoff : ℕ) (i : I) : List V :=
  (rows i).filter fun v => decide (i ∈ degreeComponentSelection rows width cutoff v)

/-- Keep the selected vertices within each path component. -/
def clipShortReturnPathComponents (rows : I → List V) (width cutoff : ℕ) (i : I) : List V :=
  (rows i).filter fun v => decide (v ∈ pathComponentSelection rows width cutoff i)

/-- Sum the sizes beyond the width in the distinct degree components. -/
def shortReturnDegreeExcessMass (rows : I → List V) (width cutoff : ℕ) : ℕ :=
  ∑ v, ∑ group ∈ linkedGroupComponents (occurrences (fun j => (rows j).toFinset) v)
    (shortReturnCopyRowGraph rows cutoff v), (group.card - width)

/-- Sum the sizes beyond the width in the distinct row components. -/
def shortReturnPathExcessMass (rows : I → List V) (width cutoff : ℕ) : ℕ :=
  ∑ i, ∑ group ∈ linkedGroupComponents (rows i).toFinset (shortReturnRowGraph rows cutoff i),
    (group.card - width)

private theorem clipDegree_sublist (rows : I → List V) (width cutoff : ℕ) (i : I) :
    (clipShortReturnDegreeComponents rows width cutoff i).Sublist (rows i) := List.filter_sublist

omit [LinearOrder I] in
theorem clipShortReturnPathComponents_sublist (rows : I → List V) (width cutoff : ℕ) (i : I) :
    (clipShortReturnPathComponents rows width cutoff i).Sublist (rows i) := List.filter_sublist

private theorem clipDegree_occurrences (rows : I → List V) (width cutoff : ℕ) (v : V) :
    occurrences (fun i => (clipShortReturnDegreeComponents rows width cutoff i).toFinset) v =
      degreeComponentSelection rows width cutoff v := by
  ext i
  simp only [mem_occurrences, List.mem_toFinset, clipShortReturnDegreeComponents, List.mem_filter, decide_eq_true_eq]
  refine ⟨And.right, fun kept => ⟨?_, kept⟩⟩
  have original := selectLinkedGroups_subset (occurrences (fun j => (rows j).toFinset) v)
    (shortReturnCopyRowGraph rows cutoff v) width kept
  exact List.mem_toFinset.mp ((mem_occurrences (marks := fun j => (rows j).toFinset)).mp original)

omit [LinearOrder I] in
private theorem clipPath_vertices (rows : I → List V) (width cutoff : ℕ) (i : I) :
    (clipShortReturnPathComponents rows width cutoff i).toFinset = pathComponentSelection rows width cutoff i := by
  ext v
  simp only [List.mem_toFinset, clipShortReturnPathComponents, List.mem_filter, decide_eq_true_eq]
  refine ⟨And.right, fun kept => ⟨?_, kept⟩⟩
  exact List.mem_toFinset.mp (selectLinkedGroups_subset (rows i).toFinset (shortReturnRowGraph rows cutoff i) width kept)

/-- Clipping the degree components loses exactly their total excess. -/
theorem clipShortReturnDegreeComponents_mass (rows : I → List V) (simple : ∀ i, (rows i).Nodup)
    (width cutoff : ℕ) :
    (∑ i, (clipShortReturnDegreeComponents rows width cutoff i).length) +
      shortReturnDegreeExcessMass rows width cutoff = ∑ i, (rows i).length := by
  let clipped := clipShortReturnDegreeComponents rows width cutoff
  let marks := fun i => (clipped i).toFinset
  let excess (v : V) := ∑ group ∈ linkedGroupComponents (occurrences (fun j => (rows j).toFinset) v)
    (shortReturnCopyRowGraph rows cutoff v), (group.card - width)
  have equal (i : I) : (marks i).card = (clipped i).length :=
    List.toFinset_card_of_nodup ((clipDegree_sublist rows width cutoff i).nodup (simple i))
  have selectedMass : (∑ i, (clipped i).length) = ∑ v, (degreeComponentSelection rows width cutoff v).card := calc
    _ = ∑ i, (marks i).card := sum_congr rfl (fun i _ => (equal i).symm)
    _ = ∑ v, (occurrences marks v).card := (sum_occurrences marks).symm
    _ = _ := sum_congr rfl (fun v _ => congrArg card (clipDegree_occurrences rows width cutoff v))
  rw [selectedMass]
  change (∑ v, (degreeComponentSelection rows width cutoff v).card) + (∑ v, excess v) = _
  calc
    _ = ∑ v, ((degreeComponentSelection rows width cutoff v).card + excess v) :=
      (sum_add_distrib (s := univ) (f := fun v => (degreeComponentSelection rows width cutoff v).card) (g := excess)).symm
    _ = ∑ v, (occurrences (fun j => (rows j).toFinset) v).card :=
      sum_congr rfl (fun v _ => selectLinkedGroups_card_add_excess
        (occurrences (fun j => (rows j).toFinset) v) (shortReturnCopyRowGraph rows cutoff v) width)
    _ = ∑ i, (rows i).toFinset.card := sum_occurrences _
    _ = _ := sum_congr rfl (fun i _ => List.toFinset_card_of_nodup (simple i))

omit [LinearOrder I] in
/-- Clipping the path components loses exactly their total excess. -/
theorem clipShortReturnPathComponents_mass (rows : I → List V) (simple : ∀ i, (rows i).Nodup)
    (width cutoff : ℕ) :
    (∑ i, (clipShortReturnPathComponents rows width cutoff i).length) +
      shortReturnPathExcessMass rows width cutoff = ∑ i, (rows i).length := by
  let clipped := clipShortReturnPathComponents rows width cutoff
  let excess (i : I) := ∑ group ∈ linkedGroupComponents (rows i).toFinset (shortReturnRowGraph rows cutoff i),
    (group.card - width)
  change (∑ i, (clipped i).length) + (∑ i, excess i) = _
  calc
    _ = ∑ i, ((clipped i).length + excess i) :=
      (sum_add_distrib (s := univ) (f := fun i => (clipped i).length) (g := excess)).symm
    _ = _ := by
      apply sum_congr rfl
      intro i _
      have widthCount : (clipped i).length = (pathComponentSelection rows width cutoff i).card :=
        (List.toFinset_card_of_nodup ((clipShortReturnPathComponents_sublist rows width cutoff i).nodup (simple i))).symm.trans
          (congrArg card (clipPath_vertices rows width cutoff i))
      rw [widthCount, ← List.toFinset_card_of_nodup (simple i)]
      exact selectLinkedGroups_card_add_excess (rows i).toFinset (shortReturnRowGraph rows cutoff i) width

private theorem clipDegree_room (rows : I → List V) (simple : ∀ i, (rows i).Nodup) (width cutoff : ℕ)
    (v : V) (i : I) (on : v ∈ clipShortReturnDegreeComponents rows width cutoff i) :
    (shortReturnCopyRowComponent (clipShortReturnDegreeComponents rows width cutoff) cutoff v i).card ≤ width := by
  let clipped := clipShortReturnDegreeComponents rows width cutoff
  have original := (clipDegree_sublist rows width cutoff i).subset on
  have chosen : shortReturnCopyRowComponent clipped cutoff v i ⊆
      degreeComponentSelection rows width cutoff v ∩ shortReturnCopyRowComponent rows cutoff v i := by
    intro j member
    have appears : j ∈ occurrences (fun i => (clipped i).toFinset) v := (mem_filter.mp member).1
    rw [clipDegree_occurrences rows width cutoff v] at appears
    exact mem_inter.mpr ⟨appears, shortReturnCopyRowComponent_subset_of_sublist simple
      (clipDegree_sublist rows width cutoff) cutoff v i member⟩
  have count := selectLinkedGroups_component_card (occurrences (fun j => (rows j).toFinset) v)
    (shortReturnCopyRowGraph rows cutoff v) width (mem_occurrences.mpr (List.mem_toFinset.mpr original))
  exact (card_le_card chosen).trans (count.trans_le (min_le_left _ _))

omit [LinearOrder I] in
theorem clipShortReturnPathComponents_room (rows : I → List V) (simple : ∀ i, (rows i).Nodup) (width cutoff : ℕ)
    (i : I) (v : V) (on : v ∈ clipShortReturnPathComponents rows width cutoff i) :
    (shortReturnRowComponent (clipShortReturnPathComponents rows width cutoff) cutoff i v).card ≤ width := by
  let clipped := clipShortReturnPathComponents rows width cutoff
  have original := (clipShortReturnPathComponents_sublist rows width cutoff i).subset on
  have chosen : shortReturnRowComponent clipped cutoff i v ⊆
      pathComponentSelection rows width cutoff i ∩ shortReturnRowComponent rows cutoff i v := by
    intro x member
    have appears : x ∈ (clipped i).toFinset := (mem_filter.mp member).1
    rw [clipPath_vertices rows width cutoff i] at appears
    exact mem_inter.mpr ⟨appears, shortReturnRowComponent_subset_of_sublist simple
      (clipShortReturnPathComponents_sublist rows width cutoff) cutoff i v member⟩
  have count := selectLinkedGroups_component_card (rows i).toFinset
    (shortReturnRowGraph rows cutoff i) width (List.mem_toFinset.mpr original)
  exact (card_le_card chosen).trans (count.trans_le (min_le_left _ _))

/-- Clip the degree components before computing the path components.
Both chosen widths hold on the result, and the exact total loss is the
sum of the two successive component excesses. -/
theorem clipShortReturnComponents_spec (rows : I → List V) (simple : ∀ i, (rows i).Nodup) (D L cutoff : ℕ) :
    let degreeKept := clipShortReturnDegreeComponents rows D cutoff
    let kept := clipShortReturnPathComponents degreeKept L cutoff
    (∀ i, (kept i).Sublist (rows i)) ∧
      (∀ v i, v ∈ kept i → (shortReturnCopyRowComponent kept cutoff v i).card ≤ D) ∧
      (∀ i, ∀ v ∈ kept i, (shortReturnRowComponent kept cutoff i v).card ≤ L) ∧
      (∑ i, (kept i).length) + (shortReturnDegreeExcessMass rows D cutoff +
        shortReturnPathExcessMass degreeKept L cutoff) = ∑ i, (rows i).length := by
  let degreeKept := clipShortReturnDegreeComponents rows D cutoff
  let kept := clipShortReturnPathComponents degreeKept L cutoff
  have simpleKept (i : I) : (degreeKept i).Nodup := (clipDegree_sublist rows D cutoff i).nodup (simple i)
  refine ⟨fun i => (clipShortReturnPathComponents_sublist degreeKept L cutoff i).trans (clipDegree_sublist rows D cutoff i), ?_,
    clipShortReturnPathComponents_room degreeKept simpleKept L cutoff, ?_⟩
  · intro v i on
    exact (card_le_card (shortReturnCopyRowComponent_subset_of_sublist simpleKept
      (clipShortReturnPathComponents_sublist degreeKept L cutoff) cutoff v i)).trans
      (clipDegree_room rows simple D cutoff v i ((clipShortReturnPathComponents_sublist degreeKept L cutoff i).subset on))
  · have v := clipShortReturnDegreeComponents_mass rows simple D cutoff
    have i := clipShortReturnPathComponents_mass degreeKept simpleKept L cutoff
    change (∑ i, (degreeKept i).length) + shortReturnDegreeExcessMass rows D cutoff = _ at v
    change (∑ i, (kept i).length) + shortReturnPathExcessMass degreeKept L cutoff = _ at i
    change (∑ i, (kept i).length) + (shortReturnDegreeExcessMass rows D cutoff +
      shortReturnPathExcessMass degreeKept L cutoff) = _
    omega

/-- At the original widths, clipping at most one third
of the mass in successive component excesses gives an indexed frozen
witness of mass at least one eighteenth. -/
theorem regularization_list_frozen_of_small_short_return_excess {n p k : ℕ} {half : Bool}
    (rows : Fin p → List (Fin n)) (simple : ∀ i, (rows i).Nodup)
    (free : localOrderAdmissible half k rows)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (rows i).length) (long : p ≤ ∑ i, (rows i).length)
    (excess : let M := ∑ i, (rows i).length
      let D := 4*M/n
      let L := 4*M/p
      3*(shortReturnDegreeExcessMass rows D k +
        shortReturnPathExcessMass (clipShortReturnDegreeComponents rows D k) L k) ≤ M) :
    let M := ∑ i, (rows i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 18*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧
      frozenListCaps n p M clean := by
  let M := ∑ i, (rows i).length
  let D := 4*M/n
  let L := 4*M/p
  let degreeKept := clipShortReturnDegreeComponents rows D k
  let kept := clipShortReturnPathComponents degreeKept L k
  obtain ⟨sub, degree, path, total⟩ := clipShortReturnComponents_spec rows simple D L k
  change (∑ i, (kept i).length) + (shortReturnDegreeExcessMass rows D k +
    shortReturnPathExcessMass degreeKept L k) = M at total
  change 3*(shortReturnDegreeExcessMass rows D k + shortReturnPathExcessMass degreeKept L k) ≤ M at excess
  exact regularization_list_frozen_of_short_return_restriction rows simple free hn hp dense long kept
    sub degree path (by omega)

/-- For literal admissible inputs, the same excess test yields a
distinct nonempty witness at every cutoff of at least two. -/
theorem regularization_list_frozen_distinct_of_small_short_return_excess {n p k : ℕ} {half : Bool}
    (rows : Fin p → List (Fin n)) (distinct : Function.Injective rows)
    (nonempty : ∀ i, rows i ≠ []) (simple : ∀ i, (rows i).Nodup)
    (free : localOrderAdmissible half k rows) (two : 2 ≤ k)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (rows i).length)
    (excess : let M := ∑ i, (rows i).length
      let D := 4*M/n
      let L := 4*M/p
      3*(shortReturnDegreeExcessMass rows D k +
        shortReturnPathExcessMass (clipShortReturnDegreeComponents rows D k) L k) ≤ M) :
    let M := ∑ i, (rows i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      Function.Injective clean ∧ (∀ i, clean i ≠ []) ∧ (∀ i, (clean i).Nodup) ∧
      localOrderAdmissible half k clean ∧ M ≤ 18*(∑ i, (clean i).length) ∧
      (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  refine regularization_list_frozen_distinct_of_indexed rows distinct nonempty simple
    free two hn hp dense (by decide) ?_
  dsimp only
  exact fun long => regularization_list_frozen_of_small_short_return_excess rows simple free hn hp dense long excess

end OnlineReachabilityPreservers
