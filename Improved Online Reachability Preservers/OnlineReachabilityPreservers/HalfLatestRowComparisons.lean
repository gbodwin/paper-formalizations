import OnlineReachabilityPreservers.CyclicIntersections

/-! Missing comparisons forced by the latest nontrivial row. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

variable {I V : Type*} [Fintype V] [DecidableEq V]

/-- The strict directed comparisons along a row, including nonconsecutive pairs. -/
def rowDirectedComparisons (rows : I → List V) (i : I) : Finset (V × V) :=
  univ.filter fun pair => pair.1 ∈ rows i ∧ pair.2 ∈ rows i ∧
    (rows i).idxOf pair.1 < (rows i).idxOf pair.2

theorem mem_rowDirectedComparisons {rows : I → List V} {i : I} {x y : V} :
    (x,y) ∈ rowDirectedComparisons rows i ↔ Before rows i x y := by
  simp [rowDirectedComparisons, SourceAudit.BeforeIn]

/-- A simple row supplies one comparison per pair of positions. -/
theorem rowDirectedComparisons_card {rows : I → List V} {i : I} (simple : (rows i).Nodup) :
    (rowDirectedComparisons rows i).card = (rows i).length.choose 2 := by
  let row := rows i
  have rowSimple : row.Nodup := simple
  let pairs : Finset (Fin row.length × Fin row.length) := univ.filter fun pair => pair.1 < pair.2
  have count : pairs.card = row.length.choose 2 := by
    simpa only [pairs, Fintype.card_fin] using (Fintype.card_product_filter_lt (α := Fin row.length))
  change (rowDirectedComparisons rows i).card = row.length.choose 2
  rw [← count]
  symm
  apply card_bij (fun pair _ => (row[pair.1.val]'pair.1.isLt, row[pair.2.val]'pair.2.isLt))
  · intro pair on
    apply mem_rowDirectedComparisons.mpr
    refine ⟨List.getElem_mem _, List.getElem_mem _, ?_⟩
    change row.idxOf (row[pair.1.val]'pair.1.isLt) < row.idxOf (row[pair.2.val]'pair.2.isLt)
    rw [rowSimple.idxOf_getElem pair.1.val pair.1.isLt,
      rowSimple.idxOf_getElem pair.2.val pair.2.isLt]
    exact (mem_filter.mp on).2
  · intro pair _ other _ equal
    exact Prod.ext (Fin.ext (simple.getElem_inj.mp (congrArg Prod.fst equal)))
      (Fin.ext (simple.getElem_inj.mp (congrArg Prod.snd equal)))
  · rintro ⟨x,y⟩ on
    have step := mem_rowDirectedComparisons.mp on
    let a : Fin row.length := ⟨row.idxOf x, List.idxOf_lt_length_of_mem step.1⟩
    let b : Fin row.length := ⟨row.idxOf y, List.idxOf_lt_length_of_mem step.2.1⟩
    exact ⟨(a,b), mem_filter.mpr ⟨mem_univ _, step.2.2⟩,
      Prod.ext (List.getElem_idxOf a.isLt) (List.getElem_idxOf b.isLt)⟩

variable [Fintype I]

/-- The directed comparisons supplied by the whole family. -/
def familyDirectedComparisons (rows : I → List V) : Finset (V × V) :=
  univ.biUnion (rowDirectedComparisons rows)

theorem mem_familyDirectedComparisons {rows : I → List V} {x y : V} :
    (x,y) ∈ familyDirectedComparisons rows ↔ ∃ i, Before rows i x y := by
  simp [familyDirectedComparisons, mem_rowDirectedComparisons]

theorem familyDirectedComparisons_subset_offDiag (rows : I → List V) :
    familyDirectedComparisons rows ⊆ (univ : Finset V).offDiag := by
  rintro ⟨x,y⟩ occupied
  obtain ⟨_,step⟩ := mem_familyDirectedComparisons.mp occupied
  exact mem_offDiag.mpr ⟨mem_univ _, mem_univ _, listBefore_ne step⟩

variable [LinearOrder I]

/-- At half cutoff two or above, no comparison contributes on two rows. -/
theorem familyDirectedComparisons_card {rows : I → List V} {cutoff : ℕ}
    (simple : ∀ i, (rows i).Nodup) (free : HalfBridgeFree (Before rows) cutoff) (enough : 2 ≤ cutoff) :
    (familyDirectedComparisons rows).card = ∑ i, (rows i).length.choose 2 := by
  classical
  have separated : ((univ : Finset I) : Set I).PairwiseDisjoint (rowDirectedComparisons rows) := by
    intro i _ j _ different
    refine disjoint_left.mpr ?_
    rintro ⟨x,y⟩ one two
    exact no_parallel_list_steps free enough different (mem_rowDirectedComparisons.mp one)
      (mem_rowDirectedComparisons.mp two)
  rw [familyDirectedComparisons, card_biUnion separated]
  exact sum_congr rfl fun i _ => rowDirectedComparisons_card (simple i)

omit [Fintype V] [Fintype I] [LinearOrder I] in
private theorem two_le_row_length_of_before {rows : I → List V} {i : I} {x y : V}
    (step : Before rows i x y) : 2 ≤ (rows i).length := by
  have right := List.idxOf_lt_length_of_mem step.2.1
  have ordered := step.2.2
  omega

/-- A comparison on the latest nontrivial row admits no two-step detour
through a vertex outside that row. Such a detour would put the last arc before
the river, or repeat a comparison if both arcs were on the same row. -/
theorem halfBridgeFree_latest_row_missing_detour {rows : I → List V}
    (free : HalfBridgeFree (Before rows) 3) {r : I}
    (latest : ∀ j, r < j → (rows j).length ≤ 1) {x y z : V}
    (river : Before rows r x y) (outside : z ∉ rows r) :
    (x,z) ∉ familyDirectedComparisons rows ∨ (z,y) ∉ familyDirectedComparisons rows := by
  by_contra! present
  obtain ⟨a,first⟩ := mem_familyDirectedComparisons.mp present.1
  obtain ⟨b,last⟩ := mem_familyDirectedComparisons.mp present.2
  have aOther : a ≠ r := fun same => outside (same ▸ first.2.1)
  have bOther : b ≠ r := fun same => outside (same ▸ last.1)
  have apart : a ≠ b := by
    intro same
    have next : Before rows a z y := same.symm ▸ last
    exact no_parallel_list_steps free (by decide) aOther
      ⟨first.1, next.2.1, first.2.2.trans next.2.2⟩ river
  have earlier : b < r := by
    apply lt_of_le_of_ne _ bOther
    apply le_of_not_gt
    intro later
    have long := two_le_row_length_of_before last
    have short := latest b later
    omega
  exact free (by decide) (threeListBridge apart aOther.symm bOther.symm first last river) earlier

/-- Each consecutive comparison on the latest row and each outside vertex
force a different missing directed pair. -/
theorem halfBridgeFree_latest_row_comparison_bound {rows : I → List V}
    (free : HalfBridgeFree (Before rows) 3) {r : I} (simple : (rows r).Nodup)
    (latest : ∀ j, r < j → (rows j).length ≤ 1) :
    (familyDirectedComparisons rows).card +
      ((rows r).length - 1) * (Fintype.card V - (rows r).length) ≤
      Fintype.card V * Fintype.card V - Fintype.card V := by
  classical
  let row := rows r
  let outside := (univ : Finset V) \ row.toFinset
  let seen := familyDirectedComparisons rows
  let all := (univ : Finset V).offDiag
  let gaps := Fin (row.length - 1)
  let start (i : gaps) : V := row[i.val]'(by have := i.isLt; omega)
  let finish (i : gaps) : V := row[i.val+1]'(by have := i.isLt; omega)
  have startOn (i : gaps) : start i ∈ row := List.getElem_mem _
  have finishOn (i : gaps) : finish i ∈ row := List.getElem_mem _
  have startInj : Function.Injective start := by
    intro i j same
    exact Fin.ext (simple.getElem_inj.mp same)
  have finishInj : Function.Injective finish := by
    intro i j same
    have next : i.val + 1 = j.val + 1 := simple.getElem_inj.mp same
    exact Fin.ext (by omega)
  have consecutive (i : gaps) : Before rows r (start i) (finish i) := by
    refine ⟨startOn i, finishOn i, ?_⟩
    dsimp [start, finish, row]
    rw [simple.idxOf_getElem, simple.idxOf_getElem]
    omega
  have off (x : ↑outside) : x.val ∉ row := by
    exact fun on => (mem_sdiff.mp x.property).2 (List.mem_toFinset.mpr on)
  let charge (sample : gaps × ↑outside) : V × V :=
    if (start sample.1, sample.2.val) ∉ seen then (start sample.1, sample.2.val)
    else (sample.2.val, finish sample.1)
  have missing (sample : gaps × ↑outside) : charge sample ∈ all \ seen := by
    rcases sample with ⟨i,z⟩
    have detour := halfBridgeFree_latest_row_missing_detour free latest (consecutive i) (off z)
    by_cases left : (start i,z.val) ∉ seen
    · simp only [charge, ite_eq_left left]
      exact mem_sdiff.mpr ⟨mem_offDiag.mpr ⟨mem_univ _, mem_univ _,
        fun same => by
          change start i = z.val at same
          exact off z (same ▸ startOn i)⟩, left⟩
    · simp only [charge, ite_eq_right left]
      exact mem_sdiff.mpr ⟨mem_offDiag.mpr ⟨mem_univ _, mem_univ _,
        fun same => by
          change z.val = finish i at same
          exact off z (same.symm ▸ finishOn i)⟩, detour.resolve_left left⟩
  have chargeInj : Function.Injective charge := by
    rintro ⟨i,z⟩ ⟨j,w⟩ equal
    by_cases leftI : (start i,z.val) ∉ seen <;> by_cases leftJ : (start j,w.val) ∉ seen
    · simp only [charge, ite_eq_left leftI, ite_eq_left leftJ] at equal
      exact Prod.ext (startInj (congrArg Prod.fst equal)) (Subtype.ext (congrArg Prod.snd equal))
    · simp only [charge, ite_eq_left leftI, ite_eq_right leftJ] at equal
      have inside : start i = w.val := congrArg Prod.fst equal
      exact (off w (inside ▸ startOn i)).elim
    · simp only [charge, ite_eq_right leftI, ite_eq_left leftJ] at equal
      have inside : start j = z.val := (congrArg Prod.fst equal).symm
      exact (off z (inside ▸ startOn j)).elim
    · simp only [charge, ite_eq_right leftI, ite_eq_right leftJ] at equal
      exact Prod.ext (finishInj (congrArg Prod.snd equal)) (Subtype.ext (congrArg Prod.fst equal))
  have count := Fintype.card_le_of_injective (fun s => (⟨charge s, missing s⟩ : ↑(all \ seen)))
    (fun _ _ equal => chargeInj (congrArg Subtype.val equal))
  have outsideCount : outside.card = Fintype.card V - row.length := by
    dsimp [outside]
    rw [card_sdiff_of_subset (subset_univ _), card_univ, List.toFinset_card_of_nodup simple]
  have contained : seen ⊆ all := familyDirectedComparisons_subset_offDiag rows
  have seenCount := card_le_card contained
  have allCount : all.card = Fintype.card V * Fintype.card V - Fintype.card V := by
    simp [all, offDiag_card]
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe, outsideCount,
    card_sdiff_of_subset contained, gaps] at count
  change seen.card + (row.length - 1) * (Fintype.card V - row.length) ≤ _
  rw [← allCount]
  omega

end OnlineReachabilityPreservers
