import OnlineReachabilityPreservers.ComponentSplitCleaning
import OnlineReachabilityPreservers.OppositeLinkForest

/-! Consequences of half-five exclusion for opposite links. -/

namespace OnlineReachabilityPreservers

open Finset

local notation "Before" => SourceAudit.BeforeIn

variable {I V : Type*} [LinearOrder I] [DecidableEq V]

private abbrev HalfFiveLink {paths : I → List V} (free : HalfBridgeFree (Before paths) 5) (x y : V) : Prop :=
  (oppositeLinkGraphOfHalfTwo paths (fun _ h => free (h.trans (by decide)))).Adj x y

private theorem halfFive_forbid_earlier_chain {paths : I → List V}
    (free : HalfBridgeFree (Before paths) 5) {river : I} {length : ℕ} (positive : 0 < length)
    (short : length ≤ 4) (v : ℕ → V)
    (injective : ∀ i ≤ length, ∀ j ≤ length, v i = v j → i = j)
    (riverStep : Before paths river (v 0) (v length))
    (steps : ∀ i < length, ∃ a < river, Before paths a (v i) (v (i+1)))
    (noGap : ∀ {a i j}, i+1 < j → j < length →
      v i ∈ paths a → v (i+1) ∈ paths a → v j ∈ paths a → v (j+1) ∈ paths a → False) : False := by
  classical
  let label (i : ℕ) := if h : i < length then (steps i h).choose else river
  have on (i : ℕ) (hi : i < length) : label i < river ∧ Before paths (label i) (v i) (v (i+1)) := by
    simpa only [label,dite_eq_left hi] using (steps i hi).choose_spec
  have shorten (i j : ℕ) (ordered : i ≤ j) (fit : j < length) (same : label i = label j) :
      Before paths (label i) (v i) (v (j+1)) := by
    have first := (on i (ordered.trans_lt fit)).2
    have last := same.symm ▸ (on j fit).2
    have adjacent : j ≤ i+1 := by
      by_contra! gap
      exact noGap gap fit first.1 first.2.1 last.1 last.2.1
    rcases (show i = j ∨ i+1 = j by omega) with equal | next
    · simpa only [equal] using first
    · have tail : Before paths (label i) (v (i+1)) (v (j+1)) := next.symm ▸ last
      exact ⟨first.1,tail.2.1,first.2.2.trans tail.2.2⟩
  obtain ⟨d,count,b,same,last⟩ := bridge_from_forward_repetitions (Before paths) v label river length
    positive injective riverStep (fun i h => (on i h).1.ne.symm) shorten
  exact free (k := d) (by omega) b (by rw [same,last]; exact (on (length-1) (by omega)).1)

private theorem halfFive_pentagon_row_all_of_four {paths : I → List V}
    (free : HalfBridgeFree (Before paths) 5) (v : Fin 5 → V) (injective : Function.Injective v)
    (side : ∀ i, HalfFiveLink free (v i) (v (i+1))) {row : I}
    (large : 4 ≤ (univ.filter fun i => v i ∈ paths row).card) : ∀ i, v i ∈ paths row := by
  classical
  intro missing
  by_contra absent
  have present {j : Fin 5} (different : j ≠ missing) : v j ∈ paths row := by
    by_contra missingTwo
    have subset : (univ.filter fun i => v i ∈ paths row) ⊆ (univ : Finset (Fin 5)) \ {missing,j} := by
      intro i on
      have belongs := (mem_filter.mp on).2
      simp only [mem_sdiff,mem_univ,mem_insert,mem_singleton,true_and,not_or]
      exact ⟨fun eq => absent (eq ▸ belongs),fun eq => missingTwo (eq ▸ belongs)⟩
    have size := card_le_card subset
    have count : ((univ : Finset (Fin 5)) \ {missing,j}).card = 3 := by
      rw [card_sdiff_of_subset (subset_univ _),card_insert_of_notMem (by simpa using different.symm)]
      simp
    omega
  have three : HalfBridgeFree (Before paths) 3 := fun _ h => free (h.trans (by decide))
  have middle {a b c : Fin 5} (ab : b = a+1) (bc : c = b+1) (ac : a ≠ c)
      (first : v a ∈ paths row) (last : v c ∈ paths row) : v b ∈ paths row :=
    halfThree_middle_on_line three first last (injective.ne ac)
      (by simpa only [← ab] using side a) (by simpa only [← bc] using side b)
  fin_cases missing
  · exact absent (middle (a := 4) (b := 0) (c := 1) (by decide) (by decide) (by decide)
      (present (by decide)) (present (by decide)))
  · exact absent (middle (a := 0) (b := 1) (c := 2) (by decide) (by decide) (by decide)
      (present (by decide)) (present (by decide)))
  · exact absent (middle (a := 1) (b := 2) (c := 3) (by decide) (by decide) (by decide)
      (present (by decide)) (present (by decide)))
  · exact absent (middle (a := 2) (b := 3) (c := 4) (by decide) (by decide) (by decide)
      (present (by decide)) (present (by decide)))
  · exact absent (middle (a := 3) (b := 4) (c := 0) (by decide) (by decide) (by decide)
      (present (by decide)) (present (by decide)))

private theorem halfFive_pentagon_no_four {paths : I → List V}
    (free : HalfBridgeFree (Before paths) 5) (v : Fin 5 → V) (injective : Function.Injective v)
    (side : ∀ i, HalfFiveLink free (v i) (v (i+1)))
    (notAll : ∀ r, ¬ ∀ i, v i ∈ paths r) {row : I} (indices : Fin 4 → Fin 5)
    (distinct : Function.Injective indices) (owned : ∀ i, v (indices i) ∈ paths row) : False := by
  classical
  apply notAll row
  apply halfFive_pentagon_row_all_of_four free v injective side
  change (univ : Finset (Fin 4)).card ≤ _
  exact card_le_card_of_injOn indices (fun i _ => mem_filter.mpr ⟨mem_univ _,owned i⟩) distinct.injOn


/-- A pair of opposite steps on paths earlier than the specified river. -/
private def EarlierOpposite {paths : I → List V} (river : I) (x y : V) : Prop :=
  ∃ a b, a < river ∧ b < river ∧ Before paths a x y ∧ Before paths b y x

private theorem EarlierOpposite.symm {paths : I → List V} {river : I} {x y : V}
    (step : EarlierOpposite (paths := paths) river x y) :
    EarlierOpposite (paths := paths) river y x := by
  obtain ⟨a,b,pa,pb,forwards,backwards⟩ := step
  exact ⟨b,a,pb,pa,backwards,forwards⟩

private theorem halfFive_forbid_earlier_pentagon_route {paths : I → List V}
    (free : HalfBridgeFree (Before paths) 5) (v : Fin 5 → V) (injective : Function.Injective v)
    (side : ∀ i, HalfFiveLink free (v i) (v (i+1))) (notAll : ∀ r, ¬ ∀ i, v i ∈ paths r)
    {n : ℕ} (positive : 0 < n) (short : n ≤ 4) {river : I} (seq : Fin (n+1) → Fin 5)
    (distinct : Function.Injective seq)
    (first : v (seq 0) ∈ paths river) (last : v (seq (Fin.last n)) ∈ paths river)
    (each : ∀ i : Fin n, EarlierOpposite (paths := paths) river (v (seq i.castSucc)) (v (seq i.succ))) :
    False := by
  have directed (route : Fin (n+1) → Fin 5) (different : Function.Injective route)
      (riverStep : Before paths river (v (route 0)) (v (route (Fin.last n))))
      (edges : ∀ i : Fin n, EarlierOpposite (paths := paths) river (v (route i.castSucc)) (v (route i.succ))) :
      False := by
    let position (i : ℕ) : Fin (n+1) := ⟨i % (n+1),Nat.mod_lt _ (by omega)⟩
    have coordinate (i : ℕ) (fit : i ≤ n) : (position i).val = i := Nat.mod_eq_of_lt (by omega)
    let index (i : ℕ) := route (position i)
    let vertex (i : ℕ) := v (index i)
    have distinctIndex (i : ℕ) (hi : i ≤ n) (j : ℕ) (hj : j ≤ n) (equal : index i = index j) : i = j := by
      have same := congrArg Fin.val (different equal)
      rwa [coordinate i hi,coordinate j hj] at same
    have corners : Before paths river (vertex 0) (vertex n) := by
      have start : position 0 = 0 := Fin.ext (coordinate 0 (by omega))
      have endPos : position n = Fin.last n := Fin.ext (coordinate n le_rfl)
      simpa only [vertex,index,start,endPos] using riverStep
    have on (i : ℕ) (hi : i < n) : ∃ a < river, Before paths a (vertex i) (vertex (i+1)) := by
      let slot : Fin n := ⟨i,hi⟩
      have start : position i = slot.castSucc := Fin.ext (coordinate i (by omega))
      have endPos : position (i+1) = slot.succ := Fin.ext (coordinate (i+1) (by omega))
      obtain ⟨a,_,early,_,step,_⟩ := edges slot
      exact ⟨a,early,by simpa only [vertex,index,start,endPos] using step⟩
    apply halfFive_forbid_earlier_chain free positive short vertex
      (fun i hi j hj equal => distinctIndex i hi j hj (injective equal)) corners on
    intro a i j gap fit u x y z
    let slots : Fin 4 → ℕ := ![i,i+1,j,j+1]
    have slotBound (s : Fin 4) : slots s ≤ n := by
      fin_cases s <;> simp [slots] <;> omega
    have slotDistinct : Function.Injective slots := by
      intro s t eq
      fin_cases s <;> fin_cases t <;> simp [slots] at eq ⊢ <;> omega
    have onRow (s : Fin 4) : v (index (slots s)) ∈ paths a := by
      fin_cases s
      · exact u
      · exact x
      · exact y
      · exact z
    exact halfFive_pentagon_no_four free v injective side notAll (index ∘ slots)
      (fun s t equal => slotDistinct (distinctIndex (slots s) (slotBound s) (slots t) (slotBound t) equal))
      onRow
  have endpoints : v (seq 0) ≠ v (seq (Fin.last n)) :=
    injective.ne (distinct.ne (by intro equal; have same := congrArg Fin.val equal; simp only [Fin.val_zero,Fin.val_last] at same; omega))
  rcases listBefore_total first last endpoints with forward | backward
  · exact directed seq distinct forward each
  · apply directed (seq ∘ Fin.rev) (distinct.comp Fin.rev_injective)
      (by simpa only [Function.comp_apply,Fin.rev_zero,Fin.rev_last] using backward)
    intro i
    simpa only [Function.comp_apply,Fin.rev_castSucc,Fin.rev_succ] using (each i.rev).symm


/-- In a five-cycle of opposite links under half-five exclusion, some
row must contain all five vertices. -/
theorem halfFive_opposite_pentagon_requires_spanning_row {paths : I → List V}
    (free : HalfBridgeFree (Before paths) 5) (v : Fin 5 → V) (injective : Function.Injective v)
    (side : ∀ i, (oppositeLinkGraphOfHalfTwo paths (fun _ h => free (h.trans (by decide)))).Adj
      (v i) (v (i+1))) : ∃ row, ∀ i, v i ∈ paths row := by
  classical
  by_contra! noAll
  have witnesses (i : Fin 5) : ∃ a b, OppositeNeighbors paths a b (v i) (v (i+1)) := side i
  choose a b both using witnesses
  let owner (slot : Fin 5 × Bool) := if slot.2 then a slot.1 else b slot.1
  obtain ⟨chosen,_,largest⟩ := exists_max_image (univ : Finset (Fin 5 × Bool))
    owner ⟨(0,false),mem_univ _⟩
  let river := owner chosen
  let w (i : Fin 5) := v (chosen.1+i)
  have rotated : Function.Injective w := fun i j eq => add_left_cancel (injective eq)
  have edges (i : Fin 5) : HalfFiveLink free (w i) (w (i+1)) := by
    simpa only [w,← add_assoc] using side (chosen.1+i)
  have notAll (r : I) : ¬ ∀ i, w i ∈ paths r := by
    intro all
    obtain ⟨i,absent⟩ := noAll r
    apply absent
    simpa [w,add_comm,sub_add_cancel] using all (i-chosen.1)
  have start : w 0 ∈ paths river ∧ w 1 ∈ paths river := by
    cases selection : chosen.2
    · have rev := (both chosen.1).2.2.1
      simpa [w,river,owner,selection] using And.intro rev.2.1 rev.1
    · have fwd := (both chosen.1).2.1
      simpa [w,river,owner,selection] using And.intro fwd.1 fwd.2.1
  have earlier (i : Fin 5) (outside : w i ∉ paths river ∨ w (i+1) ∉ paths river) :
      EarlierOpposite (paths := paths) river (w i) (w (i+1)) := by
    let j := chosen.1+i
    have fwd : Before paths (a j) (w i) (w (i+1)) := by
      simpa only [w,← add_assoc] using (both j).2.1
    have rev : Before paths (b j) (w (i+1)) (w i) := by
      simpa only [w,← add_assoc] using (both j).2.2.1
    have ale : a j ≤ river := by simpa [owner,river] using largest (j,true) (mem_univ _)
    have ble : b j ≤ river := by simpa [owner,river] using largest (j,false) (mem_univ _)
    have notRiver (r : I) (first : w i ∈ paths r) (last : w (i+1) ∈ paths r) : r ≠ river :=
      fun equal => outside.elim (fun missing => missing (equal ▸ first)) (fun missing => missing (equal ▸ last))
    exact ⟨a j,b j,ale.lt_of_ne (notRiver _ fwd.1 fwd.2.1),ble.lt_of_ne (notRiver _ rev.2.1 rev.1),fwd,rev⟩
  have forbidFour (indices : Fin 4 → Fin 5) (distinct : Function.Injective indices)
      (onRow : ∀ i, w (indices i) ∈ paths river) : False :=
    halfFive_pentagon_no_four free w rotated edges notAll indices distinct onRow
  by_cases third : w 2 ∈ paths river
  · have away3 : w 3 ∉ paths river := fun on =>
      forbidFour ![0,1,2,3] (by intro i j eq; fin_cases i <;> fin_cases j <;> (first | rfl | exact (of_decide_eq_false (by decide) eq).elim))
        (by intro i; fin_cases i; exacts [start.1,start.2,third,on])
    have away4 : w 4 ∉ paths river := fun on =>
      forbidFour ![0,1,2,4] (by intro i j eq; fin_cases i <;> fin_cases j <;> (first | rfl | exact (of_decide_eq_false (by decide) eq).elim))
        (by intro i; fin_cases i; exacts [start.1,start.2,third,on])
    refine halfFive_forbid_earlier_pentagon_route free w rotated edges notAll (n := 3)
      (by decide) (by decide) ![0,4,3,2]
      (by intro i j eq; fin_cases i <;> fin_cases j <;> (first | rfl | exact (of_decide_eq_false (by decide) eq).elim)) start.1 third ?_
    intro i
    fin_cases i
    · exact (earlier 4 (Or.inl away4)).symm
    · exact (earlier 3 (Or.inl away3)).symm
    · exact (earlier 2 (Or.inr away3)).symm
  · by_cases last : w 4 ∈ paths river
    · have away3 : w 3 ∉ paths river := fun on =>
        forbidFour ![0,1,3,4] (by intro i j eq; fin_cases i <;> fin_cases j <;> (first | rfl | exact (of_decide_eq_false (by decide) eq).elim))
          (by intro i; fin_cases i; exacts [start.1,start.2,on,last])
      refine halfFive_forbid_earlier_pentagon_route free w rotated edges notAll (n := 3)
        (by decide) (by decide) ![1,2,3,4]
        (by intro i j eq; fin_cases i <;> fin_cases j <;> (first | rfl | exact (of_decide_eq_false (by decide) eq).elim)) start.2 last ?_
      intro i
      fin_cases i
      · exact earlier 1 (Or.inr third)
      · exact earlier 2 (Or.inl third)
      · exact earlier 3 (Or.inl away3)
    · have away3 : w 3 ∉ paths river := by
        intro on
        exact third (halfThree_middle_on_line (fun _ h => free (h.trans (by decide)))
          start.2 on (rotated.ne (show (1 : Fin 5) ≠ 3 by decide)) (edges 1) (edges 2))
      refine halfFive_forbid_earlier_pentagon_route free w rotated edges notAll (n := 4)
        (by decide) (by decide) ![1,2,3,4,0]
        (by intro i j eq; fin_cases i <;> fin_cases j <;> (first | rfl | exact (of_decide_eq_false (by decide) eq).elim)) start.2 start.1 ?_
      intro i
      fin_cases i
      · exact earlier 1 (Or.inr third)
      · exact earlier 2 (Or.inl third)
      · exact earlier 3 (Or.inl away3)
      · exact earlier 4 (Or.inl last)


private abbrev rowRank {paths : I → List V} (p : I) (v : V) : ℕ := (paths p).idxOf v

private theorem spanning_pentagon_ordered_view {paths : I → List V}
    (free : HalfBridgeFree (Before paths) 5) (p : I)
    (v : Fin 5 → V) (injective : Function.Injective v)
    (side : ∀ i, HalfFiveLink free (v i) (v (i+1))) (span : ∀ i, v i ∈ paths p) :
    ∃ w : Fin 5 → V, Function.Injective w ∧ (∀ i, HalfFiveLink free (w i) (w (i+1))) ∧
      (∀ i, w i ∈ paths p) ∧ rowRank (paths := paths) p (w 0) < rowRank (paths := paths) p (w 1) ∧
      rowRank (paths := paths) p (w 1) < rowRank (paths := paths) p (w 4) ∧
      ¬ (rowRank (paths := paths) p (w 4) < rowRank (paths := paths) p (w 3) ∧
        rowRank (paths := paths) p (w 2) < rowRank (paths := paths) p (w 1)) := by
  classical
  let r := rowRank (paths := paths) p
  obtain ⟨first,_,least⟩ := exists_min_image (univ : Finset (Fin 5)) (r ∘ v) ⟨0,mem_univ _⟩
  let z (i : Fin 5) := v (first+i)
  have distinct : Function.Injective z := fun _ _ eq => add_left_cancel (injective eq)
  have cycle (i : Fin 5) : HalfFiveLink free (z i) (z (i+1)) := by
    simpa only [z,← add_assoc] using side (first+i)
  have contained (i : Fin 5) : z i ∈ paths p := span _
  have lower (i : Fin 5) (other : i ≠ 0) : r (z 0) < r (z i) := by
    apply lt_of_le_of_ne
    · simpa [r,z] using least (first+i) (mem_univ _)
    · intro equal
      exact other (distinct ((List.idxOf_inj (contained 0)).mp equal)).symm
  have normalize (w : Fin 5 → V) (different : Function.Injective w)
      (linked : ∀ i, HalfFiveLink free (w i) (w (i+1))) (present : ∀ i, w i ∈ paths p)
      (sinkLow : r (w 0) < r (w 1)) (lowHigh : r (w 1) < r (w 4)) :
      ∃ y : Fin 5 → V, Function.Injective y ∧ (∀ i, HalfFiveLink free (y i) (y (i+1))) ∧
        (∀ i, y i ∈ paths p) ∧ r (y 0) < r (y 1) ∧ r (y 1) < r (y 4) ∧
        ¬ (r (y 4) < r (y 3) ∧ r (y 2) < r (y 1)) := by
    by_cases separated : r (w 4) < r (w 3) ∧ r (w 2) < r (w 1)
    · let permutation : Fin 5 → Fin 5 := ![2,1,0,4,3]
      have unique : Function.Injective permutation := by
        intro i j eq
        fin_cases i <;> fin_cases j <;> (first | rfl | exact (of_decide_eq_false (by decide) eq).elim)
      refine ⟨w ∘ permutation,different.comp unique,?_,fun _ => present _,
        separated.2,lowHigh.trans separated.1,?_⟩
      · intro i
        fin_cases i
        · exact (linked 1).symm
        · exact (linked 0).symm
        · exact (linked 4).symm
        · exact (linked 3).symm
        · exact (linked 2).symm
      · exact fun pair => separated.1.not_gt pair.1
    · exact ⟨w,different,linked,present,sinkLow,lowHigh,separated⟩
  have other : r (z 1) ≠ r (z 4) := by
    intro eq
    exact (by decide : (1 : Fin 5) ≠ 4) (distinct ((List.idxOf_inj (contained 1)).mp eq))
  rcases lt_or_gt_of_ne other with low | high
  · exact normalize z distinct cycle contained (lower 1 (by decide)) low
  · let permutation : Fin 5 → Fin 5 := ![0,4,3,2,1]
    have unique : Function.Injective permutation := by
      intro i j eq
      fin_cases i <;> fin_cases j <;> (first | rfl | exact (of_decide_eq_false (by decide) eq).elim)
    refine normalize (z ∘ permutation) (distinct.comp unique) ?_ (fun _ => contained _)
      (lower 4 (by decide)) high
    intro i
    fin_cases i
    · exact (cycle 4).symm
    · exact (cycle 3).symm
    · exact (cycle 2).symm
    · exact (cycle 1).symm
    · exact (cycle 0).symm

private theorem opposite_link_forced_forward_row {paths : I → List V}
    (free : HalfBridgeFree (Before paths) 5) {p : I} {x y : V}
    (forward : Before paths p x y) (link : HalfFiveLink free x y) :
    ∃ q, OppositeNeighbors paths p q x y := by
  obtain ⟨a,b,both⟩ := link
  have only : a = p := by
    by_contra apart
    exact no_parallel_list_steps free (by decide) apart both.2.1 forward
  exact ⟨b,only ▸ both⟩

omit [LinearOrder I] in
private theorem distinct_opposite_partners_at_row_min {paths : I → List V}
    {p q a : I} {x y z : V}
    (near : OppositeNeighbors paths p q x y) (far : OppositeNeighbors paths p a x z)
    (middle : Before paths p y z) : q ≠ a := by
  intro same
  exact far.2.2.2 ⟨y,near.2.1,middle,same ▸ near.2.2.1.1⟩

omit [LinearOrder I] in
private theorem distinct_opposite_partners_at_row_max {paths : I → List V}
    {p q a : I} {x y z : V}
    (far : OppositeNeighbors paths p q x z) (near : OppositeNeighbors paths p a y z)
    (middle : Before paths p x y) : q ≠ a := by
  intro same
  exact far.2.2.2 ⟨y,middle,near.2.1,same.symm ▸ near.2.2.1.2.1⟩


private theorem halfFive_forbid_spanning_chain {paths : I → List V}
    (free : HalfBridgeFree (Before paths) 5) (v : Fin 5 → V) (injective : Function.Injective v)
    (side : ∀ i, HalfFiveLink free (v i) (v (i+1))) (p : I)
    (uniqueSpan : ∀ row, (∀ i, v i ∈ paths row) → row = p)
    {d : ℕ} (short : d ≤ 3) (seq : Fin (d+2) → Fin 5) (distinct : Function.Injective seq)
    (arc : Fin (d+1) → I) (oneSpan : ∀ i j, arc i = p → arc j = p → i = j)
    (river : I) (riverStep : Before paths river (v (seq 0)) (v (seq (Fin.last (d+1)))))
    (steps : ∀ i, Before paths (arc i) (v (seq i.castSucc)) (v (seq i.succ)))
    (different : ∀ i, river ≠ arc i) (early : arc (Fin.last d) < river) : False := by
  classical
  let length := d+1
  let point (i : ℕ) : Fin (length+1) := ⟨i % (length+1),Nat.mod_lt _ (by omega)⟩
  let slot (i : ℕ) : Fin length := ⟨i % length,Nat.mod_lt _ (by omega)⟩
  let index (i : ℕ) := seq (point i)
  let vertex (i : ℕ) := v (index i)
  let label (i : ℕ) := arc (slot i)
  have pointVal (i : ℕ) (fits : i ≤ length) : (point i).val = i := Nat.mod_eq_of_lt (by omega)
  have slotVal (i : ℕ) (fits : i < length) : (slot i).val = i := Nat.mod_eq_of_lt fits
  have distinctIndex (i : ℕ) (hi : i ≤ length) (j : ℕ) (hj : j ≤ length)
      (same : index i = index j) : i = j := by
    have equal := congrArg Fin.val (distinct same)
    rwa [pointVal i hi,pointVal j hj] at equal
  have riverForward : Before paths river (vertex 0) (vertex length) := by
    have first : point 0 = 0 := Fin.ext (pointVal 0 (by omega))
    have last : point length = Fin.last length := Fin.ext (pointVal length le_rfl)
    simpa only [vertex,index,first,last] using riverStep
  have follows (i : ℕ) (fit : i < length) : Before paths (label i) (vertex i) (vertex (i+1)) := by
    have first : point i = (slot i).castSucc := Fin.ext ((pointVal i (by omega)).trans (slotVal i fit).symm)
    have last : point (i+1) = (slot i).succ := Fin.ext (by rw [pointVal _ (by omega),Fin.val_succ,slotVal i fit])
    simpa only [label,vertex,index,first,last] using steps (slot i)
  have shorten (i j : ℕ) (ordered : i ≤ j) (fit : j < length) (same : label i = label j) :
      Before paths (label i) (vertex i) (vertex (j+1)) := by
    have first := follows i (ordered.trans_lt fit)
    have last : Before paths (label i) (vertex j) (vertex (j+1)) := same.symm ▸ follows j fit
    have consecutive : j ≤ i+1 := by
      by_contra! gap
      let slots : Fin 4 → ℕ := ![i,i+1,j,j+1]
      have bounded (s : Fin 4) : slots s ≤ length := by fin_cases s <;> simp [slots] <;> omega
      have separate : Function.Injective slots := by
        intro a b equal
        fin_cases a <;> fin_cases b <;> simp [slots] at equal ⊢ <;> omega
      have contained (s : Fin 4) : v (index (slots s)) ∈ paths (label i) := by
        fin_cases s
        · exact first.1
        · exact first.2.1
        · exact last.1
        · exact last.2.1
      have count : 4 ≤ (univ.filter fun k => v k ∈ paths (label i)).card := by
        change (univ : Finset (Fin 4)).card ≤ _
        exact card_le_card_of_injOn (index ∘ slots) (fun s _ => mem_filter.mpr ⟨mem_univ _,contained s⟩)
          (show Function.Injective (index ∘ slots) from
            fun a b equal => separate (distinctIndex _ (bounded a) _ (bounded b) equal)).injOn
      have wasSpan := uniqueSpan _ (halfFive_pentagon_row_all_of_four free v injective side count)
      have spansAgain : label j = p := same.symm.trans wasSpan
      have eq := congrArg Fin.val (oneSpan (slot i) (slot j) wasSpan spansAgain)
      rw [slotVal i (by omega),slotVal j fit] at eq
      omega
    rcases (show i = j ∨ i+1 = j by omega) with sameStep | next
    · simpa only [sameStep] using first
    · have tail : Before paths (label i) (vertex (i+1)) (vertex (j+1)) := next.symm ▸ last
      exact ⟨first.1,tail.2.1,first.2.2.trans tail.2.2⟩
  obtain ⟨size,count,b,oldRiver,oldLast⟩ := bridge_from_forward_repetitions (Before paths)
    vertex label river length (by omega)
    (fun i hi j hj eq => distinctIndex i hi j hj (injective eq)) riverForward
    (fun i _ => different (slot i)) shorten
  have final : slot (length-1) = Fin.last d := Fin.ext (by rw [slotVal _ (by omega)]; rfl)
  exact free (k := size) (by omega) b (by rw [oldRiver,oldLast]; simpa only [label,final] using early)


private theorem no_spanning_opposite_pentagon {paths : I → List V}
    (free : HalfBridgeFree (Before paths) 5) (p : I)
    (v : Fin 5 → V) (injective : Function.Injective v)
    (side : ∀ i, HalfFiveLink free (v i) (v (i+1))) (span : ∀ i, v i ∈ paths p) : False := by
  classical
  obtain ⟨w,distinct,linked,present,sinkLow,lowHigh,notSeparated⟩ :=
    spanning_pentagon_ordered_view free p v injective side span
  let r := rowRank (paths := paths) p
  have unequal {i j : Fin 5} (different : i ≠ j) : r (w i) ≠ r (w j) :=
    fun eq => different (distinct ((List.idxOf_inj (present i)).mp eq))
  have ascending {i j : Fin 5} (small : r (w i) < r (w j)) : Before paths p (w i) (w j) :=
    ⟨present i,present j,small⟩
  have forwardOrReverse (i : Fin 5) : ∃ q, OppositeNeighbors paths p q (w i) (w (i+1)) ∨
      OppositeNeighbors paths p q (w (i+1)) (w i) := by
    have different : i ≠ i+1 := by
      intro eq
      have same : i+0 = i+1 := (add_zero i).trans eq
      exact (by decide : (0 : Fin 5) ≠ 1) (add_left_cancel same)
    rcases lt_or_gt_of_ne (unequal different) with forward | back
    · obtain ⟨q,cert⟩ := opposite_link_forced_forward_row free (ascending forward) (linked i)
      exact ⟨q,.inl cert⟩
    · obtain ⟨q,cert⟩ := opposite_link_forced_forward_row free (ascending back) (linked i).symm
      exact ⟨q,.inr cert⟩
  choose q witness using forwardOrReverse
  have fromLeft (i : Fin 5) (up : r (w i) < r (w (i+1))) : OppositeNeighbors paths p (q i) (w i) (w (i+1)) :=
    (witness i).resolve_right (fun back => up.not_ge back.2.1.2.2.le)
  have fromRight (i : Fin 5) (up : r (w (i+1)) < r (w i)) : OppositeNeighbors paths p (q i) (w (i+1)) (w i) :=
    (witness i).resolve_left (fun forward => up.not_ge forward.2.1.2.2.le)
  have qNe (i : Fin 5) : q i ≠ p := (witness i).elim (fun step => step.1.symm) (fun step => step.1.symm)
  have onPartner (i : Fin 5) : w i ∈ paths (q i) ∧ w (i+1) ∈ paths (q i) :=
    (witness i).elim (fun step => ⟨step.2.2.1.2.1,step.2.2.1.1⟩)
      (fun step => ⟨step.2.2.1.1,step.2.2.1.2.1⟩)
  have near := fromLeft 0 sinkLow
  have far := fromRight 4 (sinkLow.trans lowHigh)
  have distinctFinal : q 0 ≠ q 4 := distinct_opposite_partners_at_row_min near far (ascending lowHigh)
  have finalStep : Before paths (q 0) (w 1) (w 0) := near.2.2.1
  have riverStep : Before paths (q 4) (w 4) (w 0) := far.2.2.1
  have riseToken : Before paths p (w 1) (w 4) := ascending lowHigh
  have distinctView : Function.Injective (![1,4,0] : Fin 3 → Fin 5) := by
    intro i j same
    fin_cases i <;> fin_cases j <;> (first | rfl | exact (of_decide_eq_false (by decide) same).elim)
  let small : Bridge (Before paths) 1 := {
    vertex := w ∘ (![1,4,0] : Fin 3 → Fin 5)
    arc := ![p,q 4]
    river := q 0
    distinctVertices := distinct.comp distinctView
    distinctArcs := by
      intro i j eq
      fin_cases i <;> fin_cases j <;> (first | rfl | exact ((qNe 4) eq).elim | exact ((qNe 4) eq.symm).elim)
    river_ne_arc := by intro i; fin_cases i; exacts [qNe 0,distinctFinal]
    riverStep := finalStep
    arcStep := by intro i; fin_cases i; exacts [riseToken,riverStep] }
  have cannotLate : ¬ q 4 < q 0 := free (k := 1) (by decide) small
  have earlierFinal : q 0 < q 4 := (le_of_not_gt cannotLate).lt_of_ne distinctFinal
  have uniqueSpanning (row : I) (all : ∀ i, w i ∈ paths row) : row = p := by
    by_contra notSpan
    have back {i j : Fin 5} (step : Before paths p (w i) (w j)) : Before paths row (w j) (w i) := by
      rcases listBefore_total (all i) (all j) (listBefore_ne step) with parallel | reverse
      · exact (no_parallel_list_steps free (by decide) notSpan parallel step).elim
      · exact reverse
    have sameNear : q 0 = row := by
      by_contra apart
      exact no_parallel_list_steps free (by decide) apart finalStep (back near.2.1)
    have sameFar : q 4 = row := by
      by_contra apart
      exact no_parallel_list_steps free (by decide) apart riverStep (back far.2.1)
    exact distinctFinal (sameNear.trans sameFar.symm)
  have noFour {row : I} (away : row ≠ p) (corners : Fin 4 → Fin 5)
      (four : Function.Injective corners) (on : ∀ i, w (corners i) ∈ paths row) : False := by
    apply away
    apply uniqueSpanning
    apply halfFive_pentagon_row_all_of_four free w distinct linked
    change (univ : Finset (Fin 4)).card ≤ _
    exact card_le_card_of_injOn corners (fun i _ => mem_filter.mpr ⟨mem_univ _,on i⟩) four.injOn
  have farNeOne : q 4 ≠ q 1 := by
    intro same
    have also : w 1 ∈ paths (q 4) ∧ w 2 ∈ paths (q 4) := same.symm ▸ onPartner 1
    exact noFour (qNe 4) ![4,0,1,2]
      (by intro i j eq; fin_cases i <;> fin_cases j <;> (first | rfl | exact (of_decide_eq_false (by decide) eq).elim))
      (by intro i; fin_cases i; exacts [(onPartner 4).1,(onPartner 4).2,also.1,also.2])
  have farNeTwo : q 4 ≠ q 2 := by
    intro same
    have also : w 2 ∈ paths (q 4) ∧ w 3 ∈ paths (q 4) := same.symm ▸ onPartner 2
    exact noFour (qNe 4) ![4,0,2,3]
      (by intro i j eq; fin_cases i <;> fin_cases j <;> (first | rfl | exact (of_decide_eq_false (by decide) eq).elim))
      (by intro i; fin_cases i; exacts [(onPartner 4).1,(onPartner 4).2,also.1,also.2])
  have farNeThree (down : r (w 3) < r (w 4)) : q 4 ≠ q 3 := by
    have beside := fromLeft 3 down
    rcases lt_or_gt_of_ne (unequal (show (0 : Fin 5) ≠ 3 by decide)) with less | more
    · exact distinct_opposite_partners_at_row_max far beside (ascending less)
    · exact (distinct_opposite_partners_at_row_max beside far (ascending more)).symm
  have forbid {d : ℕ} (length : d ≤ 3) (seq : Fin (d+2) → Fin 5) (separate : Function.Injective seq)
      (labels : Fin (d+1) → I) (oneSpan : ∀ i j, labels i = p → labels j = p → i=j)
      (first : seq 0 = 4) (last : seq (Fin.last (d+1)) = 0) (final : labels (Fin.last d) = q 0)
      (steps : ∀ i, Before paths (labels i) (w (seq i.castSucc)) (w (seq i.succ)))
      (noRiver : ∀ i, q 4 ≠ labels i) : False :=
    halfFive_forbid_spanning_chain free w distinct linked p uniqueSpanning length seq separate labels oneSpan
      (q 4) (by rw [first,last]; exact riverStep) steps noRiver (final.symm ▸ earlierFinal)
  have stepThree (down : r (w 3) < r (w 4)) : Before paths (q 3) (w 4) (w 3) := (fromLeft 3 down).2.2.1
  have stepTwo (down : r (w 2) < r (w 3)) : Before paths (q 2) (w 3) (w 2) := (fromLeft 2 down).2.2.1
  have stepOne (down : r (w 1) < r (w 2)) : Before paths (q 1) (w 2) (w 1) := (fromLeft 1 down).2.2.1
  have downOne (up : ¬ r (w 2) < r (w 1)) : r (w 1) < r (w 2) :=
    (le_of_not_gt up).lt_of_ne (unequal (by decide))
  have downTwo (up : ¬ r (w 3) < r (w 2)) : r (w 2) < r (w 3) :=
    (le_of_not_gt up).lt_of_ne (unequal (by decide))
  have downThree (up : ¬ r (w 4) < r (w 3)) : r (w 3) < r (w 4) :=
    (le_of_not_gt up).lt_of_ne (unequal (by decide))
  by_cases firstUp : r (w 4) < r (w 3)
  · have lastDown := downOne (fun lastUp => notSeparated ⟨firstUp,lastUp⟩)
    by_cases nextUp : r (w 3) < r (w 2)
    · refine forbid (d := 2) (by decide) ![4,2,1,0]
        (by intro i j eq; fin_cases i <;> fin_cases j <;> (first | rfl | exact (of_decide_eq_false (by decide) eq).elim))
        ![p,q 1,q 0] ?_ rfl rfl rfl ?_ ?_
      · intro i j first second
        fin_cases i <;> fin_cases j <;> (first | rfl | exact (qNe _ first).elim | exact (qNe _ second).elim)
      · intro i; fin_cases i; exacts [ascending (firstUp.trans nextUp),stepOne lastDown,finalStep]
      · intro i; fin_cases i; exacts [qNe 4,farNeOne,distinctFinal.symm]
    · refine forbid (d := 3) (by decide) ![4,3,2,1,0]
        (by intro i j eq; fin_cases i <;> fin_cases j <;> (first | rfl | exact (of_decide_eq_false (by decide) eq).elim))
        ![p,q 2,q 1,q 0] ?_ rfl rfl rfl ?_ ?_
      · intro i j first second
        fin_cases i <;> fin_cases j <;> (first | rfl | exact (qNe _ first).elim | exact (qNe _ second).elim)
      · intro i; fin_cases i; exacts [ascending firstUp,stepTwo (downTwo nextUp),stepOne lastDown,finalStep]
      · intro i; fin_cases i; exacts [qNe 4,farNeTwo,farNeOne,distinctFinal.symm]
  · have firstDown := downThree firstUp
    by_cases nextUp : r (w 3) < r (w 2)
    · by_cases lastUp : r (w 2) < r (w 1)
      · refine forbid (d := 2) (by decide) ![4,3,1,0]
          (by intro i j eq; fin_cases i <;> fin_cases j <;> (first | rfl | exact (of_decide_eq_false (by decide) eq).elim))
          ![q 3,p,q 0] ?_ rfl rfl rfl ?_ ?_
        · intro i j first second
          fin_cases i <;> fin_cases j <;> (first | rfl | exact (qNe _ first).elim | exact (qNe _ second).elim)
        · intro i; fin_cases i; exacts [stepThree firstDown,ascending (nextUp.trans lastUp),finalStep]
        · intro i; fin_cases i; exacts [farNeThree firstDown,qNe 4,distinctFinal.symm]
      · refine forbid (d := 3) (by decide) ![4,3,2,1,0]
          (by intro i j eq; fin_cases i <;> fin_cases j <;> (first | rfl | exact (of_decide_eq_false (by decide) eq).elim))
          ![q 3,p,q 1,q 0] ?_ rfl rfl rfl ?_ ?_
        · intro i j first second
          fin_cases i <;> fin_cases j <;> (first | rfl | exact (qNe _ first).elim | exact (qNe _ second).elim)
        · intro i; fin_cases i; exacts [stepThree firstDown,ascending nextUp,stepOne (downOne lastUp),finalStep]
        · intro i; fin_cases i; exacts [farNeThree firstDown,qNe 4,farNeOne,distinctFinal.symm]
    · have nextDown := downTwo nextUp
      by_cases lastUp : r (w 2) < r (w 1)
      · refine forbid (d := 3) (by decide) ![4,3,2,1,0]
          (by intro i j eq; fin_cases i <;> fin_cases j <;> (first | rfl | exact (of_decide_eq_false (by decide) eq).elim))
          ![q 3,q 2,p,q 0] ?_ rfl rfl rfl ?_ ?_
        · intro i j first second
          fin_cases i <;> fin_cases j <;> (first | rfl | exact (qNe _ first).elim | exact (qNe _ second).elim)
        · intro i; fin_cases i; exacts [stepThree firstDown,stepTwo nextDown,ascending lastUp,finalStep]
        · intro i; fin_cases i; exacts [farNeThree firstDown,farNeTwo,qNe 4,distinctFinal.symm]
      · refine forbid (d := 3) (by decide) ![4,3,2,1,0]
          (by intro i j eq; fin_cases i <;> fin_cases j <;> (first | rfl | exact (of_decide_eq_false (by decide) eq).elim))
          ![q 3,q 2,q 1,q 0] ?_ rfl rfl rfl ?_ ?_
        · intro i j first _
          fin_cases i <;> fin_cases j <;> (first | rfl | exact (qNe _ first).elim)
        · intro i; fin_cases i; exacts [stepThree firstDown,stepTwo nextDown,stepOne (downOne lastUp),finalStep]
        · intro i; fin_cases i; exacts [farNeThree firstDown,farNeTwo,farNeOne,distinctFinal.symm]

/-- The graph of consecutive opposite links has no five-cycle under
half-bridge exclusion through five. -/
theorem halfFive_oppositeLinkGraph_no_pentagon {paths : I → List V}
    (free : HalfBridgeFree (Before paths) 5) (v : Fin 5 → V) (injective : Function.Injective v)
    (side : ∀ i, (oppositeLinkGraphOfHalfTwo paths (fun _ h => free (h.trans (by decide)))).Adj
      (v i) (v (i+1))) : False := by
  obtain ⟨row,all⟩ := halfFive_opposite_pentagon_requires_spanning_row free v injective side
  exact no_spanning_opposite_pentagon free row v injective side all

/-- Consecutive opposite links have no cycle of length at most five
under half-bridge exclusion through size five. -/
theorem halfFive_oppositeLinkGraph_cycle_length_gt_five {paths : I → List V}
    (free : HalfBridgeFree (Before paths) 5) {u : V}
    (cycle : (oppositeLinkGraphOfHalfTwo paths (fun _ h => free (h.trans (by decide)))).Walk u u)
    (simple : cycle.IsCycle) : 5 < cycle.length := by
  by_contra! short
  have longer := halfFour_oppositeLinkGraph_cycle_length_gt_four (fun _ h => free (h.trans (by decide)))
    cycle simple
  have five : cycle.length = 5 := by omega
  let v (i : Fin 5) := cycle.getVert i.val
  have injective : Function.Injective v := by
    intro i j same
    apply Fin.ext
    exact simple.getVert_injOn' (show i.val ≤ cycle.length-1 by have := i.isLt; omega)
      (show j.val ≤ cycle.length-1 by have := j.isLt; omega) same
  have side (i : ℕ) (inside : i < 5) : HalfFiveLink free (cycle.getVert i) (cycle.getVert (i+1)) :=
    cycle.adj_getVert_succ (inside.trans_le five.symm.le)
  have closes : cycle.getVert 5 = cycle.getVert 0 := by
    calc
      _ = cycle.getVert cycle.length := congrArg cycle.getVert five.symm
      _ = _ := by simp [SimpleGraph.Walk.getVert_length]
  apply halfFive_oppositeLinkGraph_no_pentagon free v injective
  intro i
  fin_cases i
  · exact side 0 (by decide)
  · exact side 1 (by decide)
  · exact side 2 (by decide)
  · exact side 3 (by decide)
  · change HalfFiveLink free (cycle.getVert 4) (cycle.getVert 0)
    have last : HalfFiveLink free (cycle.getVert 4) (cycle.getVert 5) := side 4 (by decide)
    exact closes ▸ last

end OnlineReachabilityPreservers
