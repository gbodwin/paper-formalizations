import OnlineReachabilityPreservers.FirstOccurrenceTrimming
import OnlineReachabilityPreservers.FrozenHalfFourConflicts
import OnlineReachabilityPreservers.HalfFiveProjection

/-! Use first-occurrence groups to remove selected opposite intersections. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

/-- Each opposite comparison uses vertices first encountered together. -/
def OppositesWithinFirstOccurrenceGroups {n p : ℕ} (rows : Fin p → List (Fin n))
    (first : Fin n → Fin p) : Prop :=
  ∀ {i j x y}, i ≠ j → Before rows i x y → Before rows j y x → first x = first y

/-- A set of incidences hits a cross-group opposite comparison by
containing one of its four endpoints with the corresponding row label. -/
def CrossGroupOppositeCover {n p : ℕ} (rows : Fin p → List (Fin n))
    (first : Fin n → Fin p) (deleted : Finset (Fin p × Fin n)) : Prop :=
  ∀ {i j x y}, i ≠ j → first x ≠ first y → Before rows i x y → Before rows j y x →
    (i,x) ∈ deleted ∨ (i,y) ∈ deleted ∨ (j,x) ∈ deleted ∨ (j,y) ∈ deleted

/-- Trim within first-occurrence groups, then erase a cover of the
original cross-group opposites. The surviving rows have unique intersections. -/
theorem HalfBridgeFree.exists_unique_intersections_after_cross_group_erasure {n p cutoff : ℕ}
    {rows : Fin p → List (Fin n)} (free : HalfBridgeFree (Before rows) cutoff) (enough : 3 ≤ cutoff)
    (simple : ∀ i, (rows i).Nodup) (hp : 0 < p) (first : Fin n → Fin p)
    (firstSpec : ∀ i, ∀ v ∈ rows i, v ∈ rows (first v) ∧ first v ≤ i)
    (deleted : Finset (Fin p × Fin n)) (cover : CrossGroupOppositeCover rows first deleted) :
    ∃ kept : Fin p → List (Fin n),
      (∀ i, (kept i).Sublist (rows i)) ∧ (∀ i, (kept i).Nodup) ∧ HalfBridgeFree (Before kept) cutoff ∧
      (∀ {i j x y}, i ≠ j → x ∈ kept i → x ∈ kept j → y ∈ kept i → y ∈ kept j → x = y) ∧
      (∑ i, (rows i).length) ≤ (∑ i, (kept i).length)+n+deleted.card := by
  obtain ⟨owner,trimmed,subTrimmed,trimmedSimple,_,keepsFirst,one,mass⟩ :=
    free.exists_first_occurrence_trim enough simple hp
  let kept := erasePieceIncidences trimmed deleted
  have sub (i : Fin p) : (kept i).Sublist (rows i) :=
    (erasePieceIncidences_sublist trimmed deleted i).trans (subTrimmed i)
  have keptSimple (i : Fin p) : (kept i).Nodup := (sub i).nodup (simple i)
  have keptFree : HalfBridgeFree (Before kept) cutoff := by
    intro size bound b earlier
    exact free bound (b.mapPaths id Function.injective_id (fun i _ _ step =>
      listBefore_of_sublist (simple i) (sub i) step)) earlier
  have sameOwner {i : Fin p} {v : Fin n} (used : v ∈ rows i) : first v = owner v := by
    have retained := (keepsFirst i v used).1
    have originally := (subTrimmed (owner v)).subset retained
    exact le_antisymm (firstSpec (owner v) v originally).2
      (keepsFirst (first v) v (firstSpec i v used).1).2
  have noOpposite {i j : Fin p} {x y : Fin n} (different : i ≠ j)
      (forward : Before kept i x y) (backward : Before kept j y x) : False := by
    have originalA := listBefore_of_sublist (simple i) (sub i) forward
    have originalB := listBefore_of_sublist (simple j) (sub j) backward
    by_cases across : first x ≠ first y
    · rcases cover different across originalA originalB with cutX | cutY | cutX | cutY
      · exact (mem_erasePieceIncidences.mp forward.1).2 cutX
      · exact (mem_erasePieceIncidences.mp forward.2.1).2 cutY
      · exact (mem_erasePieceIncidences.mp backward.2.1).2 cutX
      · exact (mem_erasePieceIncidences.mp backward.1).2 cutY
    have together : first x = first y := not_not.mp across
    have equal : owner x = owner y :=
      (sameOwner originalA.1).symm.trans (together.trans (sameOwner originalA.2.1))
    have only {q : Fin p} (other : owner x ≠ q) (onX : x ∈ kept q) (onY : y ∈ kept q) : False := by
      have xIn : x ∈ (trimmed q).toFinset.filter (fun v => owner v = owner x) :=
        mem_filter.mpr ⟨List.mem_toFinset.mpr (mem_erasePieceIncidences.mp onX).1,rfl⟩
      have yIn : y ∈ (trimmed q).toFinset.filter (fun v => owner v = owner x) :=
        mem_filter.mpr ⟨List.mem_toFinset.mpr (mem_erasePieceIncidences.mp onY).1,equal.symm⟩
      exact listBefore_ne forward (card_le_one_iff.mp (one q (owner x) other) xIn yIn)
    by_cases firstRow : owner x = i
    · exact only (fun same => different (firstRow.symm.trans same)) backward.2.1 backward.1
    · exact only firstRow forward.1 forward.2.1
  have erased : (∑ i, (kept i).length) + (pieceIncidences trimmed univ ∩ deleted).card =
      ∑ i, (trimmed i).length := erasePieceIncidences_mass_add_loss trimmedSimple univ deleted
  have paid : (pieceIncidences trimmed univ ∩ deleted).card ≤ deleted.card := card_le_card inter_subset_right
  refine ⟨kept,sub,keptSimple,keptFree,?_,by omega⟩
  intro i j x y different xOnI xOnJ yOnI yOnJ
  by_contra apart
  rcases listBefore_total xOnI yOnI apart with forward | backward
  · have reverse := (listBefore_total xOnJ yOnJ apart).resolve_left
      (no_parallel_list_steps keptFree (by omega) different forward)
    exact noOpposite different forward reverse
  · have reversed : y ≠ x := fun same => apart same.symm
    have reverse := (listBefore_total yOnJ xOnJ reversed).resolve_left
      (no_parallel_list_steps keptFree (by omega) different backward)
    exact noOpposite different backward reverse

/-- If every original opposite comparison stays within a first-occurrence
group, trimming gives pairwise intersections of size at most one. -/
theorem HalfBridgeFree.exists_unique_intersections_of_first_occurrence_opposites {n p cutoff : ℕ}
    {rows : Fin p → List (Fin n)} (free : HalfBridgeFree (Before rows) cutoff) (enough : 3 ≤ cutoff)
    (simple : ∀ i, (rows i).Nodup) (hp : 0 < p) (first : Fin n → Fin p)
    (firstSpec : ∀ i, ∀ v ∈ rows i, v ∈ rows (first v) ∧ first v ≤ i)
    (opposites : OppositesWithinFirstOccurrenceGroups rows first) :
    ∃ kept : Fin p → List (Fin n),
      (∀ i, (kept i).Sublist (rows i)) ∧ (∀ i, (kept i).Nodup) ∧ HalfBridgeFree (Before kept) cutoff ∧
      (∀ {i j x y}, i ≠ j → x ∈ kept i → x ∈ kept j → y ∈ kept i → y ∈ kept j → x = y) ∧
      (∑ i, (rows i).length) ≤ (∑ i, (kept i).length)+n := by
  have cover : CrossGroupOppositeCover rows first ∅ := by
    intro i j x y different across forward backward
    exact (across (opposites different forward backward)).elim
  obtain ⟨kept,sub,keptSimple,keptFree,unique,mass⟩ :=
    free.exists_unique_intersections_after_cross_group_erasure enough simple hp first firstSpec ∅ cover
  exact ⟨kept,sub,keptSimple,keptFree,fun {_ _ _ _} => unique,by simpa using mass⟩

/-- A small cover of cross-group opposites suffices for frozen half-five
cleaning. Above the low-mass range, the cover and the vertex-count loss
must fit in one eighth of the original mass. -/
theorem regularization_list_frozen_half_five_of_cross_group_erasure {n p : ℕ}
    (rows : Fin p → List (Fin n)) (simple : ∀ i, (rows i).Nodup)
    (free : HalfBridgeFree (Before rows) 5) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (rows i).length) (long : p ≤ ∑ i, (rows i).length)
    (first : Fin n → Fin p) (firstSpec : ∀ i, ∀ v ∈ rows i, v ∈ rows (first v) ∧ first v ≤ i)
    (deleted : Finset (Fin p × Fin n)) (cover : CrossGroupOppositeCover rows first deleted)
    (budget : 8*max n p < (∑ i, (rows i).length) → 8*(n+deleted.card) ≤ ∑ i, (rows i).length) :
    let M := ∑ i, (rows i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (Before clean) 5 ∧
      M ≤ 32*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (rows i).length
  by_cases low : M ≤ 8*max n p
  · obtain ⟨n',vertices,p',paths,clean,cleanSimple,cleanFree,lower,upper,caps⟩ :=
      regularization_list_frozen_low_mass_at_cutoff 5 rows simple free (by decide) hn hp dense long low
    exact ⟨n',vertices,p',paths,clean,cleanSimple,cleanFree.halfFree,by omega,upper,caps⟩
  have high : 8*max n p < M := lt_of_not_ge low
  have budgetN : 8*n ≤ M := (Nat.mul_le_mul_left 8 (le_max_left n p)).trans high.le
  have budgetP : 8*p ≤ M := (Nat.mul_le_mul_left 8 (le_max_right n p)).trans high.le
  have paid := budget high
  obtain ⟨kept,sub,keptSimple,keptFree,unique,mass⟩ :=
    free.exists_unique_intersections_after_cross_group_erasure (by decide) simple hp first firstSpec deleted cover
  have upper : (∑ i, (kept i).length) ≤ M := sum_le_sum fun i _ => (sub i).length_le
  have lower : 7*M ≤ 8*(∑ i, (kept i).length) := by omega
  have allowed := listRegularizedPaths_halfFree_five_of_unique keptSimple keptFree (fun {_ _ _ _} => unique)
    (4*M/n) (4*M/p)
  exact regularization_list_frozen_after_large_width_blocks (half := true) (k := 5) kept keptSimple allowed
    hn hp budgetN budgetP upper lower

/-- First-occurrence groups can remove the opposing comparisons before
applying the original frozen widths at half cutoff five. -/
theorem regularization_list_frozen_half_five_of_first_occurrence_opposites {n p : ℕ}
    (rows : Fin p → List (Fin n)) (simple : ∀ i, (rows i).Nodup)
    (free : HalfBridgeFree (Before rows) 5) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (rows i).length) (long : p ≤ ∑ i, (rows i).length)
    (first : Fin n → Fin p) (firstSpec : ∀ i, ∀ v ∈ rows i, v ∈ rows (first v) ∧ first v ≤ i)
    (opposites : OppositesWithinFirstOccurrenceGroups rows first) :
    let M := ∑ i, (rows i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (Before clean) 5 ∧
      M ≤ 32*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  apply regularization_list_frozen_half_five_of_cross_group_erasure rows simple free hn hp dense long
    first firstSpec ∅
  · intro i j x y different across forward backward
    exact (across (opposites different forward backward)).elim
  · intro high
    simp only [card_empty, add_zero]
    exact (Nat.mul_le_mul_left 8 (le_max_left n p)).trans high.le

/-- The cross-group erasure cover also gives the feasible literal witness. -/
theorem regularization_list_frozen_half_five_distinct_of_cross_group_erasure {n p : ℕ}
    (rows : Fin p → List (Fin n)) (distinct : Function.Injective rows) (nonempty : ∀ i, rows i ≠ [])
    (simple : ∀ i, (rows i).Nodup) (free : HalfBridgeFree (Before rows) 5)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (rows i).length)
    (first : Fin n → Fin p) (firstSpec : ∀ i, ∀ v ∈ rows i, v ∈ rows (first v) ∧ first v ≤ i)
    (deleted : Finset (Fin p × Fin n)) (cover : CrossGroupOppositeCover rows first deleted)
    (budget : 8*max n p < (∑ i, (rows i).length) → 8*(n+deleted.card) ≤ ∑ i, (rows i).length) :
    let M := ∑ i, (rows i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      Function.Injective clean ∧ (∀ i, clean i ≠ []) ∧ (∀ i, (clean i).Nodup) ∧
      HalfBridgeFree (Before clean) 5 ∧ M ≤ 32*(∑ i, (clean i).length) ∧
      (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  regularization_list_frozen_distinct_of_indexed (half := true) (k := 5) (retention := 32)
    rows distinct nonempty simple free (by decide) hn hp dense (by decide)
    (fun long => regularization_list_frozen_half_five_of_cross_group_erasure rows simple free
      hn hp dense long first firstSpec deleted cover budget)

/-- The same condition gives the frozen half-five witness for feasible
literal input. -/
theorem regularization_list_frozen_half_five_distinct_of_first_occurrence_opposites {n p : ℕ}
    (rows : Fin p → List (Fin n)) (distinct : Function.Injective rows) (nonempty : ∀ i, rows i ≠ [])
    (simple : ∀ i, (rows i).Nodup) (free : HalfBridgeFree (Before rows) 5)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (rows i).length)
    (first : Fin n → Fin p) (firstSpec : ∀ i, ∀ v ∈ rows i, v ∈ rows (first v) ∧ first v ≤ i)
    (opposites : OppositesWithinFirstOccurrenceGroups rows first) :
    let M := ∑ i, (rows i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      Function.Injective clean ∧ (∀ i, clean i ≠ []) ∧ (∀ i, (clean i).Nodup) ∧
      HalfBridgeFree (Before clean) 5 ∧ M ≤ 32*(∑ i, (clean i).length) ∧
      (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  regularization_list_frozen_distinct_of_indexed (half := true) (k := 5) (retention := 32)
    rows distinct nonempty simple free (by decide) hn hp dense (by decide)
    (fun long => regularization_list_frozen_half_five_of_first_occurrence_opposites rows simple free
      hn hp dense long first firstSpec opposites)

end OnlineReachabilityPreservers
