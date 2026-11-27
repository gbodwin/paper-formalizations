import OnlineReachabilityPreservers.FullCoveringRow

/-! Keep every first occurrence and trim repeats of its vertex group on later rows. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

/-- Every used vertex has a first row. Unused vertices may take any label. -/
theorem exists_first_occurrence_assignment {n p : ℕ} (rows : Fin p → List (Fin n)) (hp : 0 < p) :
    ∃ first : Fin n → Fin p, ∀ i, ∀ v ∈ rows i, v ∈ rows (first v) ∧ first v ≤ i := by
  let on (v : Fin n) := (univ : Finset (Fin p)).filter fun i => v ∈ rows i
  let first (v : Fin n) : Fin p := if inside : (on v).Nonempty then (on v).min' inside else ⟨0,hp⟩
  refine ⟨first, ?_⟩
  intro i v member
  have seen : i ∈ on v := mem_filter.mpr ⟨mem_univ _, member⟩
  let present : (on v).Nonempty := ⟨i,seen⟩
  simp only [first, dite_eq_left present]
  exact ⟨(mem_filter.mp ((on v).min'_mem present)).2, (on v).min'_le i seen⟩

private def takeOne {V : Type*} [LinearOrder V] (group : Finset V) : Finset V :=
  if present : group.Nonempty then {group.min' present} else ∅

private theorem takeOne_subset {V : Type*} [LinearOrder V] (group : Finset V) : takeOne group ⊆ group := by
  unfold takeOne
  split
  · rename_i present
    exact singleton_subset_iff.mpr (group.min'_mem present)
  · exact empty_subset _

private theorem takeOne_card {V : Type*} [LinearOrder V] (group : Finset V) :
    (takeOne group).card = min 1 group.card := by
  by_cases present : group.Nonempty
  · have one : 1 ≤ group.card := Nat.succ_le_of_lt (card_pos.mpr present)
    rw [takeOne, dite_eq_left present, card_singleton]
    exact (min_eq_left one).symm
  · have empty := not_nonempty_iff_eq_empty.mp present
    simp [takeOne, empty]

/-- A simple half-three-free family can keep every first occurrence and at
most one vertex from each earlier first-occurrence group on any other row.
The trimming loses at most `n` incidences in total and preserves
the original half cutoff. -/
theorem HalfBridgeFree.exists_first_occurrence_trim {n p cutoff : ℕ}
    {rows : Fin p → List (Fin n)} (free : HalfBridgeFree (Before rows) cutoff) (enough : 3 ≤ cutoff)
    (simple : ∀ i, (rows i).Nodup) (hp : 0 < p) :
    ∃ (first : Fin n → Fin p) (kept : Fin p → List (Fin n)),
      (∀ i, (kept i).Sublist (rows i)) ∧ (∀ i, (kept i).Nodup) ∧ HalfBridgeFree (Before kept) cutoff ∧
      (∀ i, ∀ v ∈ rows i, v ∈ kept (first v) ∧ first v ≤ i) ∧
      (∀ i b, b ≠ i → ((kept i).toFinset.filter fun v => first v = b).card ≤ 1) ∧
      (∑ i, (rows i).length) ≤ (∑ i, (kept i).length)+n := by
  classical
  obtain ⟨first,firstSpec⟩ := exists_first_occurrence_assignment rows hp
  let group (b : Fin p) := (rows b).toFinset.filter fun v => first v = b
  let cell (i b : Fin p) := (rows i).toFinset ∩ group b
  let picked (i b : Fin p) := if i = b then cell i b else takeOne (cell i b)
  let selected (i : Fin p) := univ.biUnion (picked i)
  let kept (i : Fin p) := (rows i).filter fun v => decide (v ∈ selected i)
  have onGroup (b : Fin p) (v : Fin n) : v ∈ group b ↔ v ∈ rows b ∧ first v = b := by
    simp only [group, mem_filter, List.mem_toFinset]
  have inCell (i b : Fin p) : cell i b = (rows i).toFinset.filter (fun v => first v = b) := by
    ext v
    simp only [cell, mem_inter, mem_filter, List.mem_toFinset, onGroup]
    constructor
    · rintro ⟨inRow,_,tag⟩
      exact ⟨inRow,tag⟩
    · rintro ⟨inRow,tag⟩
      exact ⟨inRow,tag ▸ (firstSpec i v inRow).1,tag⟩
  have pickedSubset (i b : Fin p) : picked i b ⊆ cell i b := by
    by_cases same : i=b
    · simpa only [picked, ite_eq_left same] using (Subset.rfl : cell i b ⊆ cell i b)
    · simpa only [picked, ite_eq_right same] using takeOne_subset (cell i b)
  have selectedSubset (i : Fin p) : selected i ⊆ (rows i).toFinset := by
    intro v marked
    obtain ⟨b,_,on⟩ := mem_biUnion.mp marked
    exact (mem_inter.mp (pickedSubset i b on)).1
  have keptSet (i : Fin p) : (kept i).toFinset = selected i := by
    ext v
    simp only [kept, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨And.right, fun on => ⟨List.mem_toFinset.mp (selectedSubset i on),on⟩⟩
  have keptSimple (i : Fin p) : (kept i).Nodup := (simple i).filter _
  have sublists (i : Fin p) : (kept i).Sublist (rows i) := List.filter_sublist
  have legal : HalfBridgeFree (Before kept) cutoff := by
    intro d small bridge early
    exact free small (bridge.mapPaths id Function.injective_id (fun i _ _ step =>
      listBefore_of_sublist (simple i) (sublists i) step)) early
  have keepsFirst (i : Fin p) (v : Fin n) (on : v ∈ rows i) : v ∈ kept (first v) ∧ first v ≤ i := by
    obtain ⟨atFirst,earlier⟩ := firstSpec i v on
    refine ⟨List.mem_toFinset.mp ?_,earlier⟩
    rw [keptSet]
    apply mem_biUnion.mpr
    refine ⟨first v,mem_univ _,?_⟩
    simp only [picked, ite_eq_left rfl, inCell, mem_filter, List.mem_toFinset, and_true]
    exact atFirst
  have viewed (i b : Fin p) : (kept i).toFinset.filter (fun v => first v = b) = picked i b := by
    rw [keptSet]
    ext v
    constructor
    · intro on
      obtain ⟨c,_,chosen⟩ := mem_biUnion.mp (mem_filter.mp on).1
      have asC := (onGroup c v).mp (mem_inter.mp (pickedSubset i c chosen)).2
      have asB := (mem_filter.mp on).2
      exact (asC.2.symm.trans asB) ▸ chosen
    · intro on
      exact mem_filter.mpr ⟨mem_biUnion.mpr ⟨b,mem_univ _,on⟩,
        ((onGroup b v).mp (mem_inter.mp (pickedSubset i b on)).2).2⟩
  have atMostOne (i b : Fin p) (other : b ≠ i) :
      ((kept i).toFinset.filter fun v => first v = b).card ≤ 1 := by
    rw [viewed]
    simp only [picked, ite_eq_right other.symm, takeOne_card]
    exact min_le_left _ _
  let excess (i b : Fin p) := (cell i b).card - 1
  let loss (i b : Fin p) := if i=b then 0 else excess i b
  have exactCell (i b : Fin p) : (cell i b).card = (picked i b).card + loss i b := by
    by_cases same : i=b
    · simp [picked,loss,same]
    · simp only [picked, loss, ite_eq_right same, takeOne_card, excess]
      omega
  have exactMass (i : Fin p) : (rows i).length = (kept i).length + ∑ b, loss i b := by
    have original : (rows i).length = ∑ b, (cell i b).card := by
      rw [← List.toFinset_card_of_nodup (simple i),
        card_eq_sum_card_fiberwise (f := first) (t := univ) (fun _ _ => mem_univ _)]
      simp only [inCell]
    have chosen : (kept i).length = ∑ b, (picked i b).card := by
      have apart : ((univ : Finset (Fin p)) : Set (Fin p)).PairwiseDisjoint (picked i) := by
        intro b _ c _ different
        apply disjoint_left.mpr
        intro v left right
        have asB := ((onGroup b v).mp (mem_inter.mp (pickedSubset i b left)).2).2
        have asC := ((onGroup c v).mp (mem_inter.mp (pickedSubset i c right)).2).2
        exact different (asB.symm.trans asC)
      rw [← List.toFinset_card_of_nodup (keptSimple i), keptSet]
      unfold selected
      rw [card_biUnion apart]
    rw [original, chosen, ← sum_add_distrib]
    exact sum_congr rfl fun b _ => exactCell i b
  have groupLoss (b : Fin p) : (∑ i, loss i b) ≤ (group b).card - 1 := by
    have inside (v : Fin n) (on : v ∈ group b) : v ∈ rows b := ((onGroup b v).mp on).1
    have earlier (i : Fin p) (v : Fin n) (on : v ∈ group b) (inRow : v ∈ rows i) : b ≤ i :=
      ((onGroup b v).mp on).2 ▸ (firstSpec i v inRow).2
    have restricted (i : Fin p) : ((rows i).filter fun v => decide (v ∈ group b)).length = (cell i b).card := by
      have simple' := (simple i).filter (fun v => decide (v ∈ group b))
      rw [← List.toFinset_card_of_nodup simple']
      congr 1
      ext v
      simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq, cell, mem_inter]
    have bound := free.excess_le_on_earliest_row_support enough simple b (group b) inside earlier
    simp only [restricted] at bound
    change (∑ i, excess i b) ≤ 2*((group b).card - 1) at bound
    have ownRow : cell b b = group b := inter_eq_right.mpr (fun v on => List.mem_toFinset.mpr (inside v on))
    have split := sum_erase_add (s := (univ : Finset (Fin p))) (f := fun i => excess i b) (mem_univ b)
    have otherOnly : (∑ i, loss i b) = ∑ i ∈ (univ : Finset (Fin p)).erase b, excess i b := by
      rw [← filter_ne', sum_filter]
      apply sum_congr rfl
      intro i _
      by_cases same : i=b <;> simp [loss,same]
    rw [otherOnly]
    have ownExcess : excess b b = (group b).card-1 := by simp only [excess, ownRow]
    rw [ownExcess] at split
    omega
  have atMostN : (∑ b, (group b).card) ≤ n := by
    have apart : ((univ : Finset (Fin p)) : Set (Fin p)).PairwiseDisjoint group := by
      intro b _ c _ different
      apply disjoint_left.mpr
      intro v left right
      exact different (((onGroup b v).mp left).2.symm.trans ((onGroup c v).mp right).2)
    rw [← card_biUnion apart]
    simpa only [card_univ, Fintype.card_fin] using card_le_univ (univ.biUnion group)
  have totalLoss : (∑ b, ∑ i, loss i b) ≤ n :=
    (sum_le_sum fun b _ => (groupLoss b).trans (Nat.sub_le _ _)).trans atMostN
  refine ⟨first,kept,sublists,keptSimple,legal,keepsFirst,atMostOne,?_⟩
  have split : (∑ i, (rows i).length) = ∑ i, ((kept i).length + ∑ b, loss i b) :=
    sum_congr rfl fun i _ => exactMass i
  rw [split, sum_add_distrib, sum_comm (f := loss)]
  exact Nat.add_le_add_left totalLoss _

/-- The same sublist reduction preserves the full cutoff for full input. -/
theorem BridgeFree.exists_first_occurrence_trim {n p cutoff : ℕ}
    {rows : Fin p → List (Fin n)} (free : BridgeFree (Before rows) cutoff) (enough : 3 ≤ cutoff)
    (simple : ∀ i, (rows i).Nodup) (hp : 0 < p) :
    ∃ (first : Fin n → Fin p) (kept : Fin p → List (Fin n)),
      (∀ i, (kept i).Sublist (rows i)) ∧ (∀ i, (kept i).Nodup) ∧ BridgeFree (Before kept) cutoff ∧
      (∀ i, ∀ v ∈ rows i, v ∈ kept (first v) ∧ first v ≤ i) ∧
      (∀ i b, b ≠ i → ((kept i).toFinset.filter fun v => first v = b).card ≤ 1) ∧
      (∑ i, (rows i).length) ≤ (∑ i, (kept i).length)+n := by
  obtain ⟨first,kept,sub,keptSimple,_,firstKept,single,mass⟩ :=
    free.halfFree.exists_first_occurrence_trim enough simple hp
  refine ⟨first,kept,sub,keptSimple,?_,firstKept,single,mass⟩
  intro d size
  refine ⟨fun b => (free size).false (b.mapPaths id Function.injective_id ?_)⟩
  intro i _ _ step
  exact listBefore_of_sublist (simple i) (sub i) step

end OnlineReachabilityPreservers
