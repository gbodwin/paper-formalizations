import OnlineReachabilityPreservers.FirstOccurrenceTrimming
import OnlineReachabilityPreservers.HalfFiveProjection

/-! Use first-occurrence groups to remove selected opposite intersections. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

/-- Each opposite comparison uses vertices first encountered together. -/
def OppositesWithinFirstOccurrenceGroups {n p : ℕ} (rows : Fin p → List (Fin n))
    (first : Fin n → Fin p) : Prop :=
  ∀ {i j x y}, i ≠ j → Before rows i x y → Before rows j y x → first x = first y

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
  obtain ⟨owner,kept,sub,keptSimple,keptFree,keepsFirst,one,mass⟩ :=
    free.exists_first_occurrence_trim enough simple hp
  have sameOwner {i : Fin p} {v : Fin n} (used : v ∈ rows i) : first v = owner v := by
    have retained := (keepsFirst i v used).1
    have originally := (sub (owner v)).subset retained
    exact le_antisymm (firstSpec (owner v) v originally).2
      (keepsFirst (first v) v (firstSpec i v used).1).2
  have noOpposite {i j : Fin p} {x y : Fin n} (different : i ≠ j)
      (forward : Before kept i x y) (backward : Before kept j y x) : False := by
    have originalA := listBefore_of_sublist (simple i) (sub i) forward
    have originalB := listBefore_of_sublist (simple j) (sub j) backward
    have equal : owner x = owner y :=
      (sameOwner originalA.1).symm.trans ((opposites different originalA originalB).trans (sameOwner originalA.2.1))
    have only {q : Fin p} (other : owner x ≠ q) (onX : x ∈ kept q) (onY : y ∈ kept q) : False := by
      have xIn : x ∈ (kept q).toFinset.filter (fun v => owner v = owner x) :=
        mem_filter.mpr ⟨List.mem_toFinset.mpr onX,rfl⟩
      have yIn : y ∈ (kept q).toFinset.filter (fun v => owner v = owner x) :=
        mem_filter.mpr ⟨List.mem_toFinset.mpr onY,equal.symm⟩
      exact listBefore_ne forward (card_le_one_iff.mp (one q (owner x) other) xIn yIn)
    by_cases firstRow : owner x = i
    · exact only (fun same => different (firstRow.symm.trans same)) backward.2.1 backward.1
    · exact only firstRow forward.1 forward.2.1
  refine ⟨kept,sub,keptSimple,keptFree,?_,mass⟩
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

/-- First-occurrence groups can remove the offending opposite comparisons
before applying the original frozen widths at half cutoff five. -/
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
  let M := ∑ i, (rows i).length
  by_cases low : M ≤ 8*max n p
  · obtain ⟨n',vertices,p',paths,clean,cleanSimple,cleanFree,lower,upper,caps⟩ :=
      regularization_list_frozen_low_mass_at_cutoff 5 rows simple free (by decide) hn hp dense long low
    exact ⟨n',vertices,p',paths,clean,cleanSimple,cleanFree.halfFree,by omega,upper,caps⟩
  have budgetN : 8*n ≤ M := (Nat.mul_le_mul_left 8 (le_max_left n p)).trans (Nat.le_of_lt (lt_of_not_ge low))
  have budgetP : 8*p ≤ M := (Nat.mul_le_mul_left 8 (le_max_right n p)).trans (Nat.le_of_lt (lt_of_not_ge low))
  obtain ⟨kept,sub,keptSimple,keptFree,unique,mass⟩ :=
    free.exists_unique_intersections_of_first_occurrence_opposites (by decide) simple hp first firstSpec opposites
  have upper : (∑ i, (kept i).length) ≤ M := sum_le_sum fun i _ => (sub i).length_le
  have lower : 7*M ≤ 8*(∑ i, (kept i).length) := by omega
  have allowed := listRegularizedPaths_halfFree_five_of_unique keptSimple keptFree (fun {_ _ _ _} => unique)
    (4*M/n) (4*M/p)
  exact regularization_list_frozen_after_large_width_blocks (half := true) (k := 5) kept keptSimple allowed
    hn hp budgetN budgetP upper lower

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
