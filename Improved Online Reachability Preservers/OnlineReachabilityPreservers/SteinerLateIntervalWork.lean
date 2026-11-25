import OnlineReachabilityPreservers.SteinerIntervalWork

/-! Meter the hub tie-break and thick fallback using explicit interval rows. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V : Type*} [LinearOrder V]

private theorem least?_eq_some_of_bound {rows : Finset V} {v : V}
    (inside : v ∈ rows) (lower : ∀ w ∈ rows, v ≤ w) : least? rows = some v := by
  obtain ⟨m,hm⟩ := least?_some ⟨v,inside⟩
  rw [hm,le_antisymm (least?_le hm inside) (lower _ (least?_mem hm))]

private def leastListWithWordWork : List V → Option V × ℕ
  | [] => (none,2)
  | x :: tail =>
    let rest := leastListWithWordWork tail
    (some ((rest.1.map (min x)).getD x),rest.2+7)

private theorem leastListWithWordWork_spec (rows : List V) :
    let out := leastListWithWordWork rows
    out.1 = least? rows.toFinset ∧ out.2 = 7*rows.length+2 := by
  induction rows with
  | nil => simp [leastListWithWordWork,least?]
  | cons x tail ih =>
    obtain ⟨choice,work⟩ := ih
    let rest := leastListWithWordWork tail
    change rest.1 = least? tail.toFinset at choice
    change rest.2 = 7*tail.length+2 at work
    refine ⟨?_,?_⟩
    · change some ((rest.1.map (min x)).getD x) = _
      rw [choice]
      cases tailChoice : least? tail.toFinset with
      | none =>
        have empty := least?_eq_none.mp tailChoice
        rw [List.toFinset_cons,empty]
        exact (least?_eq_some_of_bound (by simp) (by simp)).symm
      | some y =>
        have inside := least?_mem tailChoice
        have m : min x y ∈ insert x tail.toFinset := by
          rcases min_choice x y with hx | hy
          · exact mem_insert.mpr (.inl hx)
          · exact mem_insert_of_mem (hy.symm ▸ inside)
        have lower (v : V) (h : v ∈ insert x tail.toFinset) : min x y ≤ v := by
          rcases mem_insert.mp h with rfl | elsewhere
          · exact min_le_left _ _
          · exact (min_le_right _ _).trans (least?_le tailChoice elsewhere)
        exact (least?_eq_some_of_bound (by simpa only [List.toFinset_cons] using m)
          (fun v h => lower v (by rwa [List.toFinset_cons] at h))).symm
    · change rest.2+7 = 7*(tail.length+1)+2
      rw [work,Nat.mul_add,Nat.mul_one]

private def leastMultisetWithWordWork (rows : Multiset V) : Option V × ℕ :=
  Quotient.lift leastListWithWordWork (by
    intro a b together
    obtain ⟨amin,acharge⟩ := leastListWithWordWork_spec a
    obtain ⟨bmin,bcharge⟩ := leastListWithWordWork_spec b
    have same : a.toFinset = b.toFinset := by
      ext x
      simpa only [List.mem_toFinset] using together.mem_iff
    apply Prod.ext
    · exact amin.trans ((congrArg least? same).trans bmin.symm)
    · exact acharge.trans ((congrArg (fun l : ℕ => 7*l+2) together.length_eq).trans bcharge.symm)) rows

private theorem leastMultisetWithWordWork_spec (rows : Multiset V) :
    let out := leastMultisetWithWordWork rows
    out.1 = least? rows.toFinset ∧ out.2 = 7*rows.card+2 := by
  refine Quotient.inductionOn rows ?_
  intro items
  exact leastListWithWordWork_spec items

/-- Scan the restricted sample to obtain its exact least hub. -/
def hitHubFromIntervalRowsWithWordWork (sample : Finset V) (interval : DemandIntervalRows V) : Option V × ℕ :=
  let eligible := intersectWithIntervalRowsWithWordWork interval sample
  let found := leastMultisetWithWordWork eligible.1.val
  (found.1,eligible.2+found.2+4)

theorem hitHubFromIntervalRowsWithWordWork_spec (sample : Finset V) (interval : DemandIntervalRows V) :
    let out := hitHubFromIntervalRowsWithWordWork sample interval
    out.1 = least? (sample ∩ interval.vertexSet) ∧
      out.2 ≤ sample.card*(2*interval.vertices.val.length+18)+8 := by
  let eligible := intersectWithIntervalRowsWithWordWork interval sample
  let found := leastMultisetWithWordWork eligible.1.val
  obtain ⟨shape,testWork⟩ := intersectWithIntervalRowsWithWordWork_spec interval sample
  obtain ⟨least,leastWork⟩ := leastMultisetWithWordWork_spec eligible.1.val
  change eligible.1 = sample ∩ interval.vertexSet at shape
  change found.1 = least? eligible.1.val.toFinset at least
  have hex : eligible.1.val.toFinset = eligible.1 := by ext v; simp
  have size : eligible.1.card ≤ sample.card := by rw [shape]; exact card_le_card inter_subset_left
  refine ⟨?_,?_⟩
  · rw [hex,shape] at least
    exact least
  · change eligible.2+found.2+4 ≤ _
    change found.2 = 7*eligible.1.card+2 at leastWork
    rw [leastWork]
    have extra := Nat.mul_le_mul_left 7 size
    change eligible.2 ≤ sample.card*(2*interval.vertices.val.length+11)+2 at testWork
    rw [show 2*interval.vertices.val.length+18 = (2*interval.vertices.val.length+11)+7 by omega,Nat.mul_add]
    omega

variable [Fintype V]

/-- Charge the interval preparation, the sample scan and the hub choice. -/
def hitHubFromArcRowsWordBudget (n m : ℕ) : ℕ :=
  demandIntervalRowsWordBudget n m+n*(2*n+18)+12

def hitHubFromArcRowsWithWordWork (arcs : {r : List (V × V) // r.Nodup})
    (depth : ℕ) (sample : Finset V) (d : V × V) : Option V × ℕ :=
  let interval := demandIntervalRowsWithWordWork arcs d depth
  let chosen := hitHubFromIntervalRowsWithWordWork sample interval.1
  (chosen.1,interval.2+chosen.2+4)

theorem hitHubFromArcRowsWithWordWork_spec (arcs : {r : List (V × V) // r.Nodup})
    (sample : Finset V) (d : V × V) :
    let n := Fintype.card V
    let out := hitHubFromArcRowsWithWordWork arcs n sample d
    out.1 = hitHub arcs.val.toFinset sample d ∧ out.2 ≤ hitHubFromArcRowsWordBudget n arcs.val.length := by
  let n := Fintype.card V
  let interval := demandIntervalRowsWithWordWork arcs d n
  let chosen := hitHubFromIntervalRowsWithWordWork sample interval.1
  obtain ⟨vertices,_,size,_,work⟩ := demandIntervalRowsWithWordWork_spec arcs d
  obtain ⟨same,charge⟩ := hitHubFromIntervalRowsWithWordWork_spec sample interval.1
  change interval.1.vertexSet = _ at vertices
  refine ⟨same.trans (by rw [vertices,hitHub]),?_⟩
  have cap : sample.card ≤ n := card_le_univ _
  have limit : chosen.2 ≤ n*(2*n+18)+8 := charge.trans (by gcongr)
  change interval.2+chosen.2+4 ≤ demandIntervalRowsWordBudget n arcs.val.length+n*(2*n+18)+12
  change interval.2 ≤ demandIntervalRowsWordBudget n arcs.val.length at work
  omega

/-- Prepare the exact ordered source and target demand pairs used by the hub preserver. -/
def hitRequestsFromArcRowsWithWordWork (arcs : {r : List (V × V) // r.Nodup})
    (depth : ℕ) (sample : Finset V) : List (V × V) → List ((V × V) × (V × V)) × ℕ
  | [] => ([],2)
  | d :: tail =>
    let hit := hitHubFromArcRowsWithWordWork arcs depth sample d
    let rest := hitRequestsFromArcRowsWithWordWork arcs depth sample tail
    let routed := match hit.1 with
      | none => rest.1
      | some h => ((d.1,h),(h,d.2)) :: rest.1
    (routed,hit.2+rest.2+11)

theorem hitRequestsFromArcRowsWithWordWork_spec (arcs : {r : List (V × V) // r.Nodup})
    (sample : Finset V) (D : List (V × V)) :
    let n := Fintype.card V
    let out := hitRequestsFromArcRowsWithWordWork arcs n sample D
    out.1 = hitRequests arcs.val.toFinset sample D ∧
      out.2 ≤ D.length*(hitHubFromArcRowsWordBudget n arcs.val.length+11)+2 := by
  let n := Fintype.card V
  let budget := hitHubFromArcRowsWordBudget n arcs.val.length+11
  induction D with
  | nil => simp [hitRequestsFromArcRowsWithWordWork,hitRequests]
  | cons d tail ih =>
    let hit := hitHubFromArcRowsWithWordWork arcs n sample d
    let rest := hitRequestsFromArcRowsWithWordWork arcs n sample tail
    obtain ⟨same,work⟩ := hitHubFromArcRowsWithWordWork_spec arcs sample d
    obtain ⟨older,cost⟩ := ih
    change hit.1 = _ at same
    change rest.1 = _ at older
    refine ⟨?_,?_⟩
    · change (match hit.1 with
        | none => rest.1
        | some h => ((d.1,h),(h,d.2)) :: rest.1) = _
      rw [same,older]
      cases h : hitHub arcs.val.toFinset sample d <;> simp [hitRequests,h]
    · change hit.2+rest.2+11 ≤ (tail.length+1)*budget+2
      change rest.2 ≤ tail.length*budget+2 at cost
      change hit.2 ≤ hitHubFromArcRowsWordBudget n arcs.val.length at work
      have step : hit.2+11 ≤ budget := Nat.add_le_add_right work _
      rw [Nat.add_mul,Nat.one_mul]
      omega

/-- The same thickness test as the late fallback, with input demands on explicit arc rows. -/
def anyThickRequestWithIntervalRowsWork (arcs : {r : List (V × V) // r.Nodup}) (depth threshold : ℕ) :
    List (V × V) → Bool × ℕ
  | [] => (false,2)
  | d::tail =>
    let row := demandIntervalRowsWithWordWork arcs d depth
    let length := row.1.vertices.val.length
    if threshold < length then (true,row.2+length+8)
    else
      let rest := anyThickRequestWithIntervalRowsWork arcs depth threshold tail
      (rest.1,rest.2+row.2+length+8)

theorem anyThickRequestWithIntervalRowsWork_spec (arcs : {r : List (V × V) // r.Nodup})
    (threshold : ℕ) (D : List (V × V)) :
    let n := Fintype.card V
    let out := anyThickRequestWithIntervalRowsWork arcs n threshold D
    out.1 = D.any (fun d => decide (threshold < (reachInterval arcs.val.toFinset d).card)) ∧
      out.2 ≤ D.length*(demandIntervalRowsWordBudget n arcs.val.length+n+8)+2 := by
  let n := Fintype.card V
  let B := demandIntervalRowsWordBudget n arcs.val.length+n+8
  induction D with
  | nil => simp [anyThickRequestWithIntervalRowsWork]
  | cons d tail ih =>
    let row := demandIntervalRowsWithWordWork arcs d n
    let count := row.1.vertices.val.length
    let rest := anyThickRequestWithIntervalRowsWork arcs n threshold tail
    obtain ⟨vertices,_,small,_,spent⟩ := demandIntervalRowsWithWordWork_spec arcs d
    have size : count = (reachInterval arcs.val.toFinset d).card := by
      change row.1.vertexSet = reachInterval arcs.val.toFinset d at vertices
      exact (congrArg Finset.card vertices)
    have one : row.2+count+8 ≤ B := by
      change count ≤ n at small
      change row.2 ≤ demandIntervalRowsWordBudget n arcs.val.length at spent
      unfold B
      omega
    obtain ⟨same,work⟩ := ih
    change rest.2 ≤ tail.length*B+2 at work
    let choice := if threshold < count then (true,row.2+count+8) else (rest.1,rest.2+row.2+count+8)
    change choice.1 = (d::tail).any (fun p => decide (threshold < (reachInterval arcs.val.toFinset p).card)) ∧
      choice.2 ≤ (tail.length+1)*B+2
    by_cases thick : threshold < count
    · have old : threshold < (reachInterval arcs.val.toFinset d).card := size ▸ thick
      simp only [choice,thick,ite_true,List.any_cons,old,decide_true,Bool.true_or,true_and]
      exact one.trans (by change B ≤ (tail.length+1)*B+2; rw [Nat.add_mul,Nat.one_mul]; omega)
    · have old : ¬threshold < (reachInterval arcs.val.toFinset d).card := size ▸ thick
      simp only [choice,thick,ite_false,List.any_cons,old,decide_false,Bool.false_or]
      refine ⟨same,?_⟩
      rw [Nat.add_mul,Nat.one_mul]
      omega

end OnlineReachabilityPreservers
