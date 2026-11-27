import OnlineReachabilityPreservers.CyclicIntersections
import OnlineReachabilityPreservers.FrozenDistinctCleaning
import OnlineReachabilityPreservers.LocalFrozenLowMass

/-! The mass of full-bridge-free families on the support of a row. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

variable {I V : Type*} [LinearOrder I] [DecidableEq V]

/-- Other rows cannot share the start of two comparisons whose ends belong
to a reference row. Its comparison between the ends would close a full
3-bridge, and equal ends give a parallel comparison. -/
theorem BridgeFree.no_shared_start_over_row {rows : I → List V} {cutoff : ℕ}
    (free : BridgeFree (Before rows) cutoff) (enough : 3 ≤ cutoff) {r i j : I}
    (different : i ≠ j) (notRefI : i ≠ r) (notRefJ : j ≠ r) {x y z : V}
    (left : Before rows i x y) (right : Before rows j x z)
    (onY : y ∈ rows r) (onZ : z ∈ rows r) : False := by
  have ends : y ≠ z := by
    intro same
    exact no_parallel_list_steps free.halfFree (by omega) different left (same.symm ▸ right)
  rcases listBefore_total onY onZ ends with forward | backward
  · exact (free enough).false (threeListBridge notRefI different.symm notRefJ left forward right)
  · exact (free enough).false (threeListBridge notRefJ different notRefI right backward left)

variable [Fintype I]

/-- A covering row bounds the total number of consecutive comparisons
by twice its own. On the other rows, their start vertices inject into
the covering row after its first position. -/
theorem BridgeFree.excess_le_of_covering_row {rows : I → List V} {cutoff : ℕ}
    (free : BridgeFree (Before rows) cutoff) (enough : 3 ≤ cutoff)
    (simple : ∀ i, (rows i).Nodup) (r : I)
    (covers : ∀ i, ∀ v ∈ rows i, v ∈ rows r) :
    (∑ i, ((rows i).length - 1)) ≤ 2*((rows r).length - 1) := by
  classical
  let others := {i : I // i ≠ r}
  let slots := Σ i : others, Fin ((rows i.val).length - 1)
  let start (s : slots) : V := (rows s.1.val)[s.2.val]'(by have := s.2.isLt; omega)
  let finish (s : slots) : V := (rows s.1.val)[s.2.val+1]'(by have := s.2.isLt; omega)
  have step (s : slots) : Before rows s.1.val (start s) (finish s) := by
    refine ⟨List.getElem_mem _, List.getElem_mem _, ?_⟩
    dsimp [start, finish]
    rw [(simple s.1.val).idxOf_getElem, (simple s.1.val).idxOf_getElem]
    omega
  have onStart (s : slots) : start s ∈ rows r := covers _ _ (step s).1
  have onFinish (s : slots) : finish s ∈ rows r := covers _ _ (step s).2.1
  have reverse (s : slots) : Before rows r (finish s) (start s) :=
    (listBefore_total (onStart s) (onFinish s) (listBefore_ne (step s))).resolve_left
      (no_parallel_list_steps free.halfFree (by omega) s.1.property (step s))
  let rank (s : slots) : Fin ((rows r).length - 1) := ⟨(rows r).idxOf (start s) - 1, by
    have upper := List.idxOf_lt_length_of_mem (onStart s)
    have lower := (reverse s).2.2
    omega⟩
  have rankInj : Function.Injective rank := by
    intro s t equal
    have positions := congrArg Fin.val equal
    change (rows r).idxOf (start s) - 1 = (rows r).idxOf (start t) - 1 at positions
    have earlierS := (reverse s).2.2
    have earlierT := (reverse t).2.2
    have starts : start s = start t := (List.idxOf_inj (onStart s)).mp (by omega)
    rcases s with ⟨i,a⟩
    rcases t with ⟨j,b⟩
    by_cases same : i.val = j.val
    · have matchLabel : i = j := Subtype.ext same
      subst j
      have index : a.val = b.val := (simple i.val).getElem_inj.mp starts
      have matchSlot : a = b := Fin.ext index
      subst b
      rfl
    · have stepJ := step ⟨j,b⟩
      rw [← starts] at stepJ
      exact (free.no_shared_start_over_row enough same i.property j.property
        (step ⟨i,a⟩) stepJ (onFinish ⟨i,a⟩) (onFinish ⟨j,b⟩)).elim
  have count : (∑ i : others, ((rows i.val).length - 1)) ≤ (rows r).length - 1 := by
    simpa only [slots, Fintype.card_sigma, Fintype.card_fin] using Fintype.card_le_of_injective rank rankInj
  have select : ((univ : Finset I).filter fun i => i ≠ r) = (univ : Finset I).erase r := by
    ext i
    simp
  rw [show (∑ i : others, ((rows i.val).length - 1)) =
    ∑ i ∈ (univ : Finset I).erase r, ((rows i).length - 1) by
      rw [← select, ← sum_subtype_eq_sum_filter]
      apply sum_congr _ (fun _ _ => rfl)
      ext i
      simp] at count
  have sumParts := sum_erase_add (s := (univ : Finset I)) (f := fun i => (rows i).length - 1) (mem_univ r)
  omega

/-- Restrict a full-three-free family to a set contained in one row.
The total number of consecutive comparisons is at most twice the
number of vertices minus two when the support is nonempty. -/
theorem BridgeFree.excess_le_on_row_support {rows : I → List V} {cutoff : ℕ}
    (free : BridgeFree (Before rows) cutoff) (enough : 3 ≤ cutoff)
    (simple : ∀ i, (rows i).Nodup) (r : I) (support : Finset V)
    (inside : ∀ v ∈ support, v ∈ rows r) :
    (∑ i, (((rows i).filter fun v => decide (v ∈ support)).length - 1)) ≤ 2*(support.card - 1) := by
  let kept (i : I) := (rows i).filter fun v => decide (v ∈ support)
  have keptSimple (i : I) : (kept i).Nodup := (simple i).filter _
  have rowSet : (kept r).toFinset = support := by
    ext v
    simp only [kept, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨And.right, fun on => ⟨inside v on, on⟩⟩
  have covered (i : I) (v : V) (on : v ∈ kept i) : v ∈ kept r := by
    rw [← List.mem_toFinset, rowSet]
    exact of_decide_eq_true (List.mem_filter.mp on).2
  have keptFree : BridgeFree (Before kept) cutoff := by
    intro d small
    refine ⟨fun b => (free small).false (b.mapPaths id Function.injective_id ?_)⟩
    intro i x y step
    exact listBefore_of_sublist (simple i) List.filter_sublist step
  have bound := keptFree.excess_le_of_covering_row enough keptSimple r covered
  rw [← List.toFinset_card_of_nodup (keptSimple r), rowSet] at bound
  exact bound

/-- A family with `t` covering rows has mass at most `t*p + 2*n`.
Each used vertex is assigned to a covering row containing it. -/
theorem BridgeFree.mass_le_of_covering_rows {n p t cutoff : ℕ}
    {rows : Fin p → List (Fin n)} (free : BridgeFree (Before rows) cutoff) (enough : 3 ≤ cutoff)
    (simple : ∀ i, (rows i).Nodup) (reference : Fin t → Fin p) (assign : Fin n → Fin t)
    (covers : ∀ i, ∀ v ∈ rows i, v ∈ rows (reference (assign v))) :
    (∑ i, (rows i).length) ≤ t*p+2*n := by
  classical
  let used := (univ : Finset (Fin n)).filter fun v => ∃ i, v ∈ rows i
  let part (b : Fin t) := used.filter fun v => assign v = b
  let kept (b : Fin t) (i : Fin p) := (rows i).filter fun v => decide (v ∈ part b)
  have usedBound : (∑ b, (part b).card) ≤ n := by
    rw [← card_eq_sum_card_fiberwise (t := univ) (s := used) (f := assign) (fun _ _ => mem_univ _)]
    simpa only [card_univ, Fintype.card_fin] using card_le_univ used
  have setKept (i : Fin p) (b : Fin t) : (kept b i).toFinset = (rows i).toFinset.filter (fun v => assign v = b) := by
    ext v
    simp only [kept, part, used, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, mem_filter, mem_univ, true_and]
    exact ⟨fun on => ⟨on.1,on.2.2⟩, fun on => ⟨on.1,⟨i,on.1⟩,on.2⟩⟩
  have splitMass (i : Fin p) : (rows i).length = ∑ b, (kept b i).length := by
    rw [← List.toFinset_card_of_nodup (simple i),
      card_eq_sum_card_fiberwise (f := assign) (t := univ) (fun _ _ => mem_univ _)]
    apply sum_congr rfl
    intro b _
    rw [← setKept i b, List.toFinset_card_of_nodup ((simple i).filter _)]
  have partBound (b : Fin t) : (∑ i, (kept b i).length) ≤ p+2*(part b).card := by
    have inside (v : Fin n) (on : v ∈ part b) : v ∈ rows (reference b) := by
      have value := (mem_filter.mp on).2
      obtain ⟨i, member⟩ := (mem_filter.mp (mem_filter.mp on).1).2
      exact value ▸ covers i v member
    have excess : (∑ i, ((kept b i).length - 1)) ≤ 2*((part b).card - 1) :=
      free.excess_le_on_row_support enough simple (reference b) (part b) inside
    have count : (∑ i, (kept b i).length) ≤ ∑ i, ((kept b i).length - 1 + 1) :=
      sum_le_sum fun i _ => by omega
    simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id, mul_one] at count
    omega
  calc
    (∑ i, (rows i).length) = ∑ b, ∑ i, (kept b i).length := by
      simp_rw [splitMass]
      exact sum_comm
    _ ≤ ∑ b, (p+2*(part b).card) := sum_le_sum fun b _ => partBound b
    _ ≤ t*p+2*n := by
      simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id, ← mul_sum]
      omega

/-- Six covering rows suffice for frozen full-bridge cleaning at any
full cutoff of at least three. -/
theorem regularization_list_frozen_full_of_covering_rows {n p t cutoff : ℕ}
    (rows : Fin p → List (Fin n)) (simple : ∀ i, (rows i).Nodup)
    (free : BridgeFree (Before rows) cutoff) (enough : 3 ≤ cutoff)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (rows i).length) (long : p ≤ ∑ i, (rows i).length)
    (reference : Fin t → Fin p) (assign : Fin n → Fin t) (few : t ≤ 6)
    (covers : ∀ i, ∀ v ∈ rows i, v ∈ rows (reference (assign v))) :
    let M := ∑ i, (rows i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) cutoff ∧
      M ≤ 8*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  have mass := free.mass_le_of_covering_rows enough simple reference assign covers
  have demand := Nat.mul_le_mul_right p few
  have vertices := le_max_left n p
  have paths := le_max_right n p
  exact regularization_list_frozen_low_mass_at_cutoff cutoff rows simple free.halfFree (by omega)
    hn hp dense long (by omega)

/-- The same six-row cover gives a distinct nonempty frozen witness
for feasible literal input. -/
theorem regularization_list_frozen_full_distinct_of_covering_rows {n p t cutoff : ℕ}
    (rows : Fin p → List (Fin n)) (distinct : Function.Injective rows) (nonempty : ∀ i, rows i ≠ [])
    (simple : ∀ i, (rows i).Nodup) (free : BridgeFree (Before rows) cutoff) (enough : 3 ≤ cutoff)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (rows i).length)
    (reference : Fin t → Fin p) (assign : Fin n → Fin t) (few : t ≤ 6)
    (covers : ∀ i, ∀ v ∈ rows i, v ∈ rows (reference (assign v))) :
    let M := ∑ i, (rows i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      Function.Injective clean ∧ (∀ i, clean i ≠ []) ∧ (∀ i, (clean i).Nodup) ∧
      BridgeFree (Before clean) cutoff ∧ M ≤ 8*(∑ i, (clean i).length) ∧
      (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  regularization_list_frozen_distinct_of_indexed (half := false) (k := cutoff) (retention := 8)
    rows distinct nonempty simple free (by omega) hn hp dense (by decide)
    (fun long => regularization_list_frozen_full_of_covering_rows rows simple free enough hn hp dense long
      reference assign few covers)

end OnlineReachabilityPreservers
