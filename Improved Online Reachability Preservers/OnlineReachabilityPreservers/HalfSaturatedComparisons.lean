import OnlineReachabilityPreservers.HalfLatestRowComparisons
import OnlineReachabilityPreservers.ExtremalCopyBounds

/-! Saturating the directed-pair budget in the presence of a spanning row. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

variable {I V : Type*} [DecidableEq V] [LinearOrder I]

/-- Against the order of a single row, the three reverse comparisons of
a triangle must all be on the same row. Distinct rows would require two
opposite arrival orders. -/
theorem halfBridgeFree_reverse_triangle_one_row {rows : I → List V}
    (free : HalfBridgeFree (Before rows) 3) {r a b c : I} {x y z : V}
    (xy : Before rows r x y) (yz : Before rows r y z)
    (yx : Before rows a y x) (zx : Before rows b z x) (zy : Before rows c z y) :
    a = b ∧ b = c := by
  have xz : Before rows r x z := ⟨xy.1, yz.2.1, xy.2.2.trans yz.2.2⟩
  have ra : r ≠ a := fun same => lt_asymm xy.2.2 ((same.symm ▸ yx).2.2)
  have rb : r ≠ b := fun same => lt_asymm xz.2.2 ((same.symm ▸ zx).2.2)
  have equalPair : a = b ∨ a = c ∨ b = c := by
    by_contra! distinct
    rcases lt_or_gt_of_ne distinct.1 with earlier | later
    · exact free (by decide) (threeListBridge distinct.2.1.symm distinct.2.2 distinct.1.symm zy yx zx) earlier
    · exact free (by decide) (threeListBridge rb ra.symm distinct.1 yz zx yx) later
  have owners {j q : I} {u v : V} (forward : Before rows r u v) (reverse : Before rows j v u)
      (other : r ≠ q) (onU : u ∈ rows q) (onV : v ∈ rows q) : j = q := by
    have step : Before rows q v u :=
      (listBefore_total onU onV (listBefore_ne forward)).resolve_left
        (no_parallel_list_steps free (by decide) other forward)
    by_contra apart
    exact no_parallel_list_steps free (by decide) apart reverse step
  obtain ⟨q,other,onX,onY,onZ⟩ : ∃ q, r ≠ q ∧ x ∈ rows q ∧ y ∈ rows q ∧ z ∈ rows q := by
    rcases equalPair with ab | ac | bc
    · exact ⟨a,ra,yx.2.1,yx.1,ab.symm ▸ zx.1⟩
    · exact ⟨a,ra,yx.2.1,yx.1,ac.symm ▸ zy.1⟩
    · exact ⟨b,rb,zx.2.1,bc.symm ▸ zy.2.1,zx.1⟩
  have aq := owners xy yx other onX onY
  have bq := owners xz zx other onX onZ
  have cq := owners yz zy other onY onZ
  exact ⟨aq.trans bq.symm, bq.trans cq.symm⟩

/-- Two spanning rows already supply both comparisons of each pair. -/
theorem halfBridgeFree_other_row_short_of_spanning_pair {rows : I → List V}
    (free : HalfBridgeFree (Before rows) 2) {r j q : I} (separate : r ≠ j)
    (spansR : ∀ x, x ∈ rows r) (spansJ : ∀ x, x ∈ rows j)
    (otherR : q ≠ r) (otherJ : q ≠ j) (simple : (rows q).Nodup) : (rows q).length ≤ 1 := by
  by_contra! long
  let x : V := (rows q)[0]'(by omega)
  let y : V := (rows q)[1]'(by omega)
  have own : Before rows q x y := by
    refine ⟨List.getElem_mem _, List.getElem_mem _, ?_⟩
    dsimp [x,y]
    rw [simple.idxOf_getElem, simple.idxOf_getElem]
    decide
  have backR := (listBefore_total (spansR x) (spansR y) (listBefore_ne own)).resolve_left
    (no_parallel_list_steps free le_rfl otherR own)
  have forwardJ := (listBefore_total (spansJ x) (spansJ y) (listBefore_ne own)).resolve_right
    (no_parallel_list_steps free le_rfl separate backR)
  exact no_parallel_list_steps free le_rfl otherJ own forwardJ

variable [Fintype V] [Fintype I]

/-- If every directed pair occurs and one row spans the vertices, the
reverse comparison of its endpoints is on another spanning row. -/
theorem halfBridgeFree_saturated_has_second_spanning_row {rows : I → List V}
    (free : HalfBridgeFree (Before rows) 3) {r : I} (simple : (rows r).Nodup)
    (spans : ∀ x, x ∈ rows r) (long : 2 ≤ (rows r).length)
    (saturated : familyDirectedComparisons rows = (univ : Finset V).offDiag) :
    ∃ j, j ≠ r ∧ ∀ x, x ∈ rows j := by
  let row := rows r
  let first : V := row[0]'(by dsimp [row]; omega)
  let last : V := row[row.length-1]'(by dsimp [row]; omega)
  have lastIndex : row.idxOf last = row.length-1 := simple.idxOf_getElem _ _
  have firstIndex : row.idxOf first = 0 := simple.idxOf_getElem _ _
  have forward : Before rows r first last := by
    refine ⟨spans first, spans last, ?_⟩
    change row.idxOf first < row.idxOf last
    rw [firstIndex, lastIndex]
    dsimp [row]
    omega
  have paired {u v : V} (step : Before rows r u v) : ∃ i, Before rows i v u := by
    apply mem_familyDirectedComparisons.mp
    rw [saturated]
    exact mem_offDiag.mpr ⟨mem_univ _, mem_univ _, (listBefore_ne step).symm⟩
  obtain ⟨b,across⟩ := paired forward
  refine ⟨b,fun same => lt_asymm forward.2.2 ((same ▸ across).2.2),?_⟩
  intro x
  by_cases isFirst : x = first
  · exact isFirst.symm ▸ across.2.1
  by_cases isLast : x = last
  · exact isLast.symm ▸ across.1
  have beforeFirst : row.idxOf first < row.idxOf x := by
    rw [firstIndex]
    exact Nat.pos_of_ne_zero (fun same => isFirst ((List.idxOf_inj (spans x)).mp (same.trans firstIndex.symm)))
  have beforeLast : row.idxOf x < row.idxOf last := by
    have inside := List.idxOf_lt_length_of_mem (spans x)
    have unequal : row.idxOf x ≠ row.idxOf last :=
      fun same => isLast ((List.idxOf_inj (spans x)).mp same)
    change row.idxOf x < row.length at inside
    omega
  have left : Before rows r first x := ⟨spans first, spans x, beforeFirst⟩
  have right : Before rows r x last := ⟨spans x, spans last, beforeLast⟩
  obtain ⟨a,backLeft⟩ := paired left
  obtain ⟨c,backRight⟩ := paired right
  have labels := halfBridgeFree_reverse_triangle_one_row free left right backLeft across backRight
  exact labels.1 ▸ backLeft.1

namespace SourceAudit

private theorem four_vertices_five_paths_half_mass_bound (rows : Fin 5 → List (Fin 4))
    (simple : ∀ i, (rows i).Nodup) (free : HalfBridgeFree (Before rows) 3) :
    (∑ i, (rows i).length) ≤ 12 := by
  by_contra! large
  let pairs := familyDirectedComparisons rows
  let room := (univ : Finset (Fin 4)).offDiag
  have occupied : pairs ⊆ room := familyDirectedComparisons_subset_offDiag rows
  have capacity : room.card = 12 := by simp [room, offDiag_card]
  have lengths (i : Fin 5) : (rows i).length ≤ 4 := by
    rw [← List.toFinset_card_of_nodup (simple i)]
    simpa only [Fintype.card_fin] using card_le_univ (rows i).toFinset
  let bonus (i : Fin 5) : ℕ := if (rows i).length = 4 then 1 else 0
  have rowCost (i : Fin 5) : 2*(rows i).length + bonus i ≤ (rows i).length.choose 2 + 3 := by
    have upper := lengths i
    dsimp [bonus]
    interval_cases (rows i).length <;> decide
  have paid := sum_le_sum (s := univ) (fun i _ => rowCost i)
  simp only [sum_add_distrib, ← mul_sum, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul] at paid
  rw [← familyDirectedComparisons_card simple free (by decide)] at paid
  change 2 * (∑ i, (rows i).length) + (∑ i, bonus i) ≤ pairs.card + 15 at paid
  by_cases spanning : ∃ r, (rows r).length = 4
  · obtain ⟨r,full⟩ := spanning
    have oneBonus : 1 ≤ ∑ i, bonus i := by
      have chosen : bonus r ≤ ∑ i, bonus i := single_le_sum (fun i _ => Nat.zero_le (bonus i)) (mem_univ r)
      simpa [bonus,full] using chosen
    have saturated : pairs = room := eq_of_subset_of_card_le occupied (by rw [capacity]; omega)
    have rowCovers : (rows r).toFinset = univ := eq_of_subset_of_card_le (subset_univ _) (by
      rw [card_univ, Fintype.card_fin, List.toFinset_card_of_nodup (simple r), full])
    have coversR (v : Fin 4) : v ∈ rows r := List.mem_toFinset.mp (rowCovers.symm ▸ mem_univ v)
    obtain ⟨j,other,coversJ⟩ := halfBridgeFree_saturated_has_second_spanning_row free (simple r)
      coversR (by rw [full]; decide) saturated
    have freeTwo : HalfBridgeFree (Before rows) 2 := fun _ h => free (h.trans (by decide))
    have costs (i : Fin 5) : (rows i).length ≤ 1 + (if i = r then 3 else 0) + (if i = j then 3 else 0) := by
      by_cases atR : i = r
      · simpa [atR, other.symm] using lengths i
      by_cases atJ : i = j
      · simpa [atJ, other] using lengths i
      simpa [atR,atJ] using halfBridgeFree_other_row_short_of_spanning_pair freeTwo other.symm
        coversR coversJ atR atJ (simple i)
    have total : (∑ i, (rows i).length) ≤ ∑ i, (1 + (if i = r then 3 else 0) + (if i = j then 3 else 0)) :=
      sum_le_sum fun i _ => costs i
    simp [sum_add_distrib] at total
    omega
  · let active := (univ : Finset (Fin 5)).filter fun i => 2 ≤ (rows i).length
    have hasActive : active.Nonempty := by
      by_contra none
      have short (i : Fin 5) : (rows i).length ≤ 1 := by
        by_contra! long
        exact none ⟨i, mem_filter.mpr ⟨mem_univ _,long⟩⟩
      have small : (∑ i, (rows i).length) ≤ ∑ _ : Fin 5, 1 := sum_le_sum fun i _ => short i
      simp at small
      omega
    let r := active.max' hasActive
    have long : 2 ≤ (rows r).length := (mem_filter.mp (max'_mem active hasActive)).2
    have notFull : (rows r).length ≠ 4 := fun full => spanning ⟨r,full⟩
    have halfCut : (rows r).length ≤ 3 := by have := lengths r; omega
    have latest (i : Fin 5) (after : r < i) : (rows i).length ≤ 1 := by
      by_contra! long
      exact (not_lt_of_ge (le_max' active i (mem_filter.mpr ⟨mem_univ _,long⟩))) after
    have missing := halfBridgeFree_latest_row_comparison_bound free (simple r) latest
    have penalty : ((rows r).length - 1)*(4-(rows r).length) = 2 := by
      interval_cases (rows r).length <;> decide
    simp only [Fintype.card_fin, penalty] at missing
    change pairs.card + 2 ≤ 12 at missing
    omega

/-- With at most four vertices and five paths, half exclusion through
three gives at most twelve incidences. -/
theorem four_vertices_five_paths_half_mass_le_twelve {n p cutoff : ℕ}
    (rows : Fin p → List (Fin n)) (simple : ∀ i, (rows i).Nodup)
    (free : HalfBridgeFree (Before rows) cutoff) (enough : 3 ≤ cutoff)
    (vertices : n ≤ 4) (paths : p ≤ 5) : (∑ i, (rows i).length) ≤ 12 := by
  obtain ⟨padded, paddedSimple, paddedFree, sameMass⟩ :=
    exists_disjoint_copies_with_budgets (half := true) (t := 1) rows simple free
      (by simpa using vertices) (by simpa using paths)
  have bound := four_vertices_five_paths_half_mass_bound padded paddedSimple
    (fun _ size => paddedFree (size.trans enough))
  simpa [sameMass] using bound

end SourceAudit

end OnlineReachabilityPreservers
