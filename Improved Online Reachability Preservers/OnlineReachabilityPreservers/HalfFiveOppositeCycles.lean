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

end OnlineReachabilityPreservers
