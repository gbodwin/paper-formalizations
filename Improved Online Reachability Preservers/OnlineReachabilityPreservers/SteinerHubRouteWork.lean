import OnlineReachabilityPreservers.SccLiftListWork
import OnlineReachabilityPreservers.SteinerLateReplay

/-! Evaluate the two hub routing orientations and the service query with explicit lists. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V : Type*} [LinearOrder V] [Fintype V]

/-- The two lifted runs, the projected demand lists and one arc union. -/
def hubRouteListWordBudget (n m p : ℕ) : ℕ :=
  2*(1+liftCoreWordBudget n m p+(1+p*(4+forwardStepWordBudget n m))) +
    6*(m+p+n^2)+8 + (2*((2*n^2)*n^2)+16*(2*n^2)+12) + (12*p+16)

omit [Fintype V] in
/-- Run the two list-backed hub routines on already projected demand legs. -/
def hubPreserverFromLegsListWithWordWork (arcs : List (V × V)) (vertices : List V)
    (legs : List ((V × V) × (V × V))) : List (V × V) × ℕ :=
  let left := sinkPreserverListWithWordWork arcs vertices (legs.map Prod.fst)
  let right := sourcePreserverListWithWordWork arcs vertices (legs.map Prod.snd)
  let joined := left.1 ++ right.1
  let unique := insertListWithChecks joined []
  (unique.1,left.2+right.2+(2*unique.2+16*joined.length+12)+(12*legs.length+16))

theorem hubPreserverFromLegsListWithWordWork_spec (arcs : List (V × V)) (vertices : List V)
    (simple : vertices.Nodup) (complete : ∀ v : V, v ∈ vertices) (legs : List ((V × V) × (V × V))) :
    let out := hubPreserverFromLegsListWithWordWork arcs vertices legs
    out.1.Nodup ∧ out.1.toFinset =
      sinkPreserver arcs.toFinset (legs.map Prod.fst) ∪ sourcePreserver arcs.toFinset (legs.map Prod.snd) ∧
      out.2 ≤ hubRouteListWordBudget (Fintype.card V) arcs.length legs.length := by
  let n := Fintype.card V
  let m := arcs.length
  let p := legs.length
  let left := sinkPreserverListWithWordWork arcs vertices (legs.map Prod.fst)
  let right := sourcePreserverListWithWordWork arcs vertices (legs.map Prod.snd)
  let joined := left.1 ++ right.1
  let unique := insertListWithChecks joined []
  let W := 1+liftCoreWordBudget n m p+(1+p*(4+forwardStepWordBudget n m))
  obtain ⟨lSimple,lSame,lCost⟩ := sinkPreserverListWithWordWork_spec arcs vertices (legs.map Prod.fst) simple complete
  obtain ⟨rSimple,rSame,rCost⟩ := sourcePreserverListWithWordWork_spec arcs vertices (legs.map Prod.snd) simple complete
  obtain ⟨uSimple,uSame,uCost⟩ := insertListWithChecks_spec joined [] (by simp)
  change left.1.Nodup at lSimple
  change right.1.Nodup at rSimple
  have lsize : left.1.length ≤ n^2 := by
    rw [← List.toFinset_card_of_nodup lSimple, pow_two, ← show Fintype.card (V × V) = n*n by simp [n]]
    exact card_le_univ _
  have rsize : right.1.length ≤ n^2 := by
    rw [← List.toFinset_card_of_nodup rSimple, pow_two, ← show Fintype.card (V × V) = n*n by simp [n]]
    exact card_le_univ _
  have size : joined.length ≤ 2*n^2 := by
    change (left.1++right.1).length ≤ _
    rw [List.length_append]
    omega
  have shared : unique.2 ≤ (2*n^2)*n^2 := by
    change unique.2 ≤ joined.length*Fintype.card (V × V) at uCost
    have product : Fintype.card (V × V) = n^2 := by simp [n,pow_two]
    rw [product] at uCost
    exact uCost.trans (Nat.mul_le_mul_right _ size)
  have leftWork : left.2 ≤ W := by simpa only [left,W,n,m,p,List.length_map] using lCost
  have rightWork : right.2 ≤ W+6*(m+p+n^2)+8 := by simpa only [right,W,n,m,p,List.length_map] using rCost
  refine ⟨uSimple,?_,?_⟩
  · change unique.1.toFinset = _
    change unique.1.toFinset = ([] : List (V × V)).toFinset ∪ joined.toFinset at uSame
    change left.1.toFinset = _ at lSame
    change right.1.toFinset = _ at rSame
    rw [uSame,List.toFinset_nil,empty_union,show joined.toFinset = _ from List.toFinset_append,lSame,rSame]
  · change left.2+right.2+(2*unique.2+16*joined.length+12)+(12*p+16) ≤ hubRouteListWordBudget n m p
    calc
      _ ≤ W+(W+6*(m+p+n^2)+8)+(2*((2*n^2)*n^2)+16*(2*n^2)+12)+(12*p+16) := by gcongr
      _ = _ := by unfold hubRouteListWordBudget W; ring

private theorem hubRouteListWordBudget_mono (n m : ℕ) : Monotone (hubRouteListWordBudget n m) := by
  intro p q le
  unfold hubRouteListWordBudget liftCoreWordBudget
  gcongr

omit [Fintype V] in
/-- Return the hub preserver as a list and charge its preparation and routing. -/
def hubPreserverListWithWordWork (arcs : {r : List (V × V) // r.Nodup}) (depth : ℕ)
    (vertices : List V) (sample : Finset V) (D : List (V × V)) : List (V × V) × ℕ :=
  let legs := hitRequestsFromArcRowsWithWordWork arcs depth sample D
  let out := hubPreserverFromLegsListWithWordWork arcs.val vertices legs.1
  (out.1,legs.2+out.2+6)

theorem hubPreserverListWithWordWork_spec (arcs : {r : List (V × V) // r.Nodup})
    (vertices : List V) (simple : vertices.Nodup) (complete : ∀ v : V, v ∈ vertices) (sample : Finset V)
    (D : List (V × V)) :
    let n := Fintype.card V
    let m := arcs.val.length
    let p := D.length
    let out := hubPreserverListWithWordWork arcs n vertices sample D
    out.1.Nodup ∧ out.1.toFinset = hubPreserver arcs.val.toFinset sample D ∧
      out.2 ≤ p*(hitHubFromArcRowsWordBudget n m+11)+hubRouteListWordBudget n m p+8 := by
  let n := Fintype.card V
  let m := arcs.val.length
  let legs := hitRequestsFromArcRowsWithWordWork arcs n sample D
  let out := hubPreserverFromLegsListWithWordWork arcs.val vertices legs.1
  obtain ⟨exactLegs,prep⟩ := hitRequestsFromArcRowsWithWordWork_spec arcs sample D
  obtain ⟨distinct,graph,spent⟩ := hubPreserverFromLegsListWithWordWork_spec arcs.val vertices simple complete legs.1
  change legs.1 = _ at exactLegs
  have cap : legs.1.length ≤ D.length := by
    rw [exactLegs]
    exact List.length_filterMap_le _ _
  refine ⟨distinct,?_,?_⟩
  · change out.1.toFinset = _
    change out.1.toFinset = _ at graph
    simpa only [exactLegs,hubPreserver] using graph
  · change legs.2+out.2+6 ≤ D.length*(hitHubFromArcRowsWordBudget n m+11)+hubRouteListWordBudget n m D.length+8
    have prepBound : legs.2 ≤ D.length*(hitHubFromArcRowsWordBudget n m+11)+2 := prep
    have routed : out.2 ≤ hubRouteListWordBudget n m D.length := spent.trans (hubRouteListWordBudget_mono n m cap)
    omega

omit [Fintype V] in
/-- Check whether the hub output already serves an arriving pair. -/
def hubServesWithWordWork (rows : List (V × V)) (depth : ℕ) (d : V × V) : Bool × ℕ :=
  let reached := reachInListWithWordWork rows d.2 depth
  let found := memScanWithWordWork d.1 reached.1
  (found.1,reached.2+2*found.2+5)

theorem hubServesWithWordWork_spec (rows : List (V × V)) (d : V × V) :
    let n := Fintype.card V
    let out := hubServesWithWordWork rows n d
    out.1 = decide (d.1 ∈ reaches rows.toFinset d.2) ∧
      out.2 ≤ reachInListWordBudget n rows.length+4*n+7 := by
  let n := Fintype.card V
  let reached := reachInListWithWordWork rows d.2 n
  let found := memScanWithWordWork d.1 reached.1
  obtain ⟨distinct,reachedEq,arcsWork⟩ := reachInListWithWordWork_spec rows d.2 n
  obtain ⟨answer,cost⟩ := memScanWithWordWork_spec d.1 reached.1
  change reached.1.Nodup at distinct
  have limit : reached.1.length ≤ n := by
    rw [← List.toFinset_card_of_nodup distinct]
    exact card_le_univ _
  refine ⟨answer.trans ?_,?_⟩
  · apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    rw [← List.mem_toFinset]
    exact Iff.of_eq (congrArg (fun s : Finset V => d.1 ∈ s) reachedEq)
  · change reached.2+2*found.2+5 ≤ reachInListWordBudget n rows.length+4*n+7
    have first : reached.2 ≤ reachInListWordBudget n rows.length := arcsWork
    change found.2 ≤ 2*reached.1.length+1 at cost
    omega

/-- One late arrival, including two hub runs on the accepted hit trace when needed. -/
def lateHubStepWordBudget (n m p : ℕ) : ℕ :=
  hitHubFromArcRowsWordBudget n m +
    (p*(hitHubFromArcRowsWordBudget n m+11)+hubRouteListWordBudget n m p+8) +
    (reachInListWordBudget n (n^2)+4*n+7) + (10*p+28)

private theorem lateHubStepWordBudget_mono (n m : ℕ) : Monotone (lateHubStepWordBudget n m) := by
  intro p q short
  unfold lateHubStepWordBudget
  have route := hubRouteListWordBudget_mono n m short
  gcongr

omit [Fintype V] in
private def lateHubStepWithWordWork (arcs : {r : List (V × V) // r.Nodup}) (depth : ℕ)
    (vertices : List V) (sample : Finset V) (st : SteinerPhaseTraces V) (d : V × V) : SteinerPhaseTraces V × ℕ :=
  if d.1 = d.2 then (st,4)
  else
    let selected := hitHubFromArcRowsWithWordWork arcs depth sample d
    match selected.1 with
    | none =>
      let found := memScanWithWordWork d st.thin
      let next := if found.1 then st else {st with thin := st.thin++[d]}
      (next,selected.2+2*found.2+2*st.thin.length+14)
    | some _ =>
      let hubs := hubPreserverListWithWordWork arcs depth vertices sample st.hits
      let served := hubServesWithWordWork hubs.1 depth d
      let next := if served.1 then st else {st with hits := st.hits++[d]}
      (next,selected.2+hubs.2+served.2+2*st.hits.length+14)

private theorem lateHubStepWithWordWork_spec (arcs : {r : List (V × V) // r.Nodup}) (vertices : List V)
    (simple : vertices.Nodup) (complete : ∀ v : V, v ∈ vertices) (sample : Finset V)
    (st : SteinerPhaseTraces V) (d : V × V) (early : EarlySteinerRule arcs.val.toFinset)
    (p : ℕ) (fewH : st.hits.length ≤ p) (fewT : st.thin.length ≤ p) :
    let n := Fintype.card V
    let out := lateHubStepWithWordWork arcs n vertices sample st d
    out.1 = steinerPhaseStep early 0 sample st d ∧ out.1.hits.length ≤ st.hits.length+1 ∧
      out.1.thin.length ≤ st.thin.length+1 ∧ (∀ a ∈ out.1.thin, a ∈ st.thin ∨ a = d) ∧
      out.2 ≤ lateHubStepWordBudget n arcs.val.length p := by
  let n := Fintype.card V
  let m := arcs.val.length
  let selected := hitHubFromArcRowsWithWordWork arcs n sample d
  obtain ⟨same,selection⟩ := hitHubFromArcRowsWithWordWork_spec arcs sample d
  change selected.2 ≤ hitHubFromArcRowsWordBudget n m at selection
  by_cases self : d.1 = d.2
  · simp only [lateHubStepWithWordWork,steinerPhaseStep,self,ite_true,true_and]
    refine ⟨Nat.le_succ _,Nat.le_succ _,fun _ mem => Or.inl mem,?_⟩
    unfold lateHubStepWordBudget
    omega
  have hitEq : (hitHubFromArcRowsWithWordWork arcs (Fintype.card V) sample d).1 = hitHub arcs.val.toFinset sample d := same
  cases hit : hitHub arcs.val.toFinset sample d with
  | none =>
    let found := memScanWithWordWork d st.thin
    obtain ⟨answer,scan⟩ := memScanWithWordWork_spec d st.thin
    change found.2 ≤ 2*st.thin.length+1 at scan
    have bound : selected.2+2*found.2+2*st.thin.length+14 ≤ lateHubStepWordBudget n m p := by
      unfold lateHubStepWordBudget
      omega
    by_cases seen : d ∈ st.thin
    · simp only [lateHubStepWithWordWork,steinerPhaseStep,self,ite_false,Nat.not_lt_zero,hitEq,hit,answer,
        seen,decide_true,ite_true,true_and]
      exact ⟨Nat.le_succ _,Nat.le_succ _,fun _ mem => Or.inl mem,bound⟩
    · simp only [lateHubStepWithWordWork,steinerPhaseStep,self,ite_false,Nat.not_lt_zero,hitEq,hit,answer,
        seen,decide_false,Bool.false_eq_true,ite_false,true_and,List.length_append,List.length_singleton,
        le_refl,List.mem_append,List.mem_singleton]
      exact ⟨Nat.le_succ _,fun _ mem => mem,bound⟩
  | some h =>
    let hubs := hubPreserverListWithWordWork arcs n vertices sample st.hits
    let served := hubServesWithWordWork hubs.1 n d
    obtain ⟨nodup,hubExact,hubWork⟩ := hubPreserverListWithWordWork_spec arcs vertices simple complete sample st.hits
    obtain ⟨found,reachWork⟩ := hubServesWithWordWork_spec hubs.1 d
    change hubs.1.Nodup at nodup
    change hubs.1.toFinset = hubPreserver arcs.val.toFinset sample st.hits at hubExact
    change served.1 = _ at found
    rw [hubExact] at found
    have nodes : hubs.1.length ≤ n^2 := by
      rw [← List.toFinset_card_of_nodup nodup,pow_two, ← show Fintype.card (V × V) = n*n by simp [n]]
      exact card_le_univ _
    have hubCap : hubs.2 ≤ p*(hitHubFromArcRowsWordBudget n m+11)+hubRouteListWordBudget n m p+8 := by
      have monotone := hubRouteListWordBudget_mono n m fewH
      exact hubWork.trans (by gcongr)
    have reachCap : served.2 ≤ reachInListWordBudget n (n^2)+4*n+7 := by
      refine reachWork.trans ?_
      unfold reachInListWordBudget
      gcongr
    have bound : selected.2+hubs.2+served.2+2*st.hits.length+14 ≤ lateHubStepWordBudget n m p := by
      unfold lateHubStepWordBudget
      omega
    have answer : (hubServesWithWordWork
        (hubPreserverListWithWordWork arcs (Fintype.card V) vertices sample st.hits).1 (Fintype.card V) d).1 =
          decide (d.1 ∈ reaches (hubPreserver arcs.val.toFinset sample st.hits) d.2) := found
    by_cases ready : d.1 ∈ reaches (hubPreserver arcs.val.toFinset sample st.hits) d.2
    · simp only [lateHubStepWithWordWork,steinerPhaseStep,self,ite_false,Nat.not_lt_zero,hitEq,hit,answer,
        ready,decide_true,ite_true,true_and]
      exact ⟨Nat.le_succ _,Nat.le_succ _,fun _ mem => Or.inl mem,bound⟩
    · simp only [lateHubStepWithWordWork,steinerPhaseStep,self,ite_false,Nat.not_lt_zero,hitEq,hit,answer,
        ready,decide_false,Bool.false_eq_true,ite_false,true_and,
        List.length_append,List.length_singleton,le_refl]
      exact ⟨Nat.le_succ _,fun _ mem => Or.inl mem,bound⟩

omit [Fintype V] in
private def lateHubTraceWithWordWorkFrom (arcs : {r : List (V × V) // r.Nodup}) (depth : ℕ)
    (vertices : List V) (sample : Finset V) : List (V × V) → SteinerPhaseTraces V → SteinerPhaseTraces V × ℕ
  | [], st => (st,2)
  | d::tail, st =>
    let step := lateHubStepWithWordWork arcs depth vertices sample st d
    let next := lateHubTraceWithWordWorkFrom arcs depth vertices sample tail step.1
    (next.1,step.2+next.2+8)

private theorem lateHubTraceWithWordWorkFrom_spec (arcs : {r : List (V × V) // r.Nodup}) (vertices : List V)
    (simple : vertices.Nodup) (complete : ∀ v : V, v ∈ vertices) (sample : Finset V)
    (early : EarlySteinerRule arcs.val.toFinset) (D : List (V × V)) (st : SteinerPhaseTraces V)
    (p : ℕ) (fewH : st.hits.length+D.length ≤ p) (fewT : st.thin.length+D.length ≤ p) :
    let n := Fintype.card V
    let out := lateHubTraceWithWordWorkFrom arcs n vertices sample D st
    out.1 = D.foldl (steinerPhaseStep early 0 sample) st ∧
      out.1.hits.length ≤ p ∧ out.1.thin.length ≤ p ∧
      (∀ a ∈ out.1.thin, a ∈ st.thin ∨ a ∈ D) ∧
      out.2 ≤ D.length*(lateHubStepWordBudget n arcs.val.length p+8)+2 := by
  let n := Fintype.card V
  let B := lateHubStepWordBudget n arcs.val.length p+8
  induction D generalizing st with
  | nil => simpa [lateHubTraceWithWordWorkFrom] using And.intro fewH fewT
  | cons d tail ih =>
    let step := lateHubStepWithWordWork arcs n vertices sample st d
    let next := lateHubTraceWithWordWorkFrom arcs n vertices sample tail step.1
    obtain ⟨same,hits,thins,coverage,stepWork⟩ :=
      lateHubStepWithWordWork_spec arcs vertices simple complete sample st d early p (by omega) (by omega)
    change step.1 = _ at same
    change step.1.hits.length ≤ st.hits.length+1 at hits
    change step.1.thin.length ≤ st.thin.length+1 at thins
    have hRoom : step.1.hits.length+tail.length ≤ p := by simp only [List.length_cons] at fewH; omega
    have tRoom : step.1.thin.length+tail.length ≤ p := by simp only [List.length_cons] at fewT; omega
    obtain ⟨val,hcap,tcap,all,tailWork⟩ := ih step.1 hRoom tRoom
    refine ⟨val.trans (congrArg (tail.foldl (steinerPhaseStep early 0 sample)) same),hcap,tcap,?_,?_⟩
    · intro a on
      rcases all a on with old | later
      · rcases coverage a old with inherited | rfl
        · exact Or.inl inherited
        · exact Or.inr List.mem_cons_self
      · exact Or.inr (List.mem_cons_of_mem _ later)
    · change step.2+next.2+8 ≤ (tail.length+1)*B+2
      change next.2 ≤ tail.length*B+2 at tailWork
      have single : step.2+8 ≤ B := Nat.add_le_add_right stepWork 8
      rw [Nat.add_mul,Nat.one_mul]
      omega

private def unionRowsWithWordWork {A : Type*} [DecidableEq A] : List A → Finset A → Finset A × ℕ
  | [], stock => (stock,2)
  | key::tail, stock =>
    let scan := memFinsetWithWordWork key stock
    let next := if h : scan.1 = true then stock else
      Finset.cons key stock (fun mem => h ((memFinsetWithWordWork_spec key stock).1.trans (decide_eq_true mem)))
    let rest := unionRowsWithWordWork tail next
    (rest.1,scan.2+rest.2+10)

private theorem unionRowsWithWordWork_spec {A : Type*} [DecidableEq A] [Fintype A] (rows : List A) (stock : Finset A) :
    let out := unionRowsWithWordWork rows stock
    out.1 = rows.toFinset ∪ stock ∧ out.2 ≤ rows.length*(12*Fintype.card A+16)+2 := by
  let C := 12*Fintype.card A+16
  induction rows generalizing stock with
  | nil => simp [unionRowsWithWordWork]
  | cons key tail ih =>
    let scan := memFinsetWithWordWork key stock
    let next := if h : scan.1 = true then stock else
      Finset.cons key stock (fun mem => h ((memFinsetWithWordWork_spec key stock).1.trans (decide_eq_true mem)))
    let rest := unionRowsWithWordWork tail next
    obtain ⟨test,work⟩ := memFinsetWithWordWork_spec key stock
    obtain ⟨same,tailCost⟩ := ih next
    have inserted : next = insert key stock := by
      change scan.1 = _ at test
      by_cases present : key ∈ stock
      · simp [next,test,present]
      · simp [next,test,present,Finset.cons_eq_insert]
    refine ⟨?_,?_⟩
    · change rest.1 = (key::tail).toFinset ∪ stock
      change rest.1 = _ at same
      rw [same,inserted,List.toFinset_cons]
      ext a
      simp only [mem_union,mem_insert]
      tauto
    · change scan.2+rest.2+10 ≤ (tail.length+1)*C+2
      change rest.2 ≤ tail.length*C+2 at tailCost
      have one : scan.2 ≤ 12*Fintype.card A+6 := work.trans (by gcongr; exact card_le_univ _)
      have single : scan.2+10 ≤ C := by unfold C; omega
      rw [Nat.add_mul,Nat.one_mul]
      omega

def lateHubRoutingWordBudget (n m p : ℕ) : ℕ :=
  (p*(lateHubStepWordBudget n m p+8)+2) +
    (p*(demandIntervalRowsWordBudget n m+n+8)+2) +
    (p*(hitHubFromArcRowsWordBudget n m+11)+hubRouteListWordBudget n m p+8) +
    (n^2*(12*n^2+16)+2) + 20

theorem lateHubRoutingWordBudget_mono (n m : ℕ) : Monotone (lateHubRoutingWordBudget n m) := by
  intro a b short
  have step := lateHubStepWordBudget_mono n m short
  have route := hubRouteListWordBudget_mono n m short
  unfold lateHubRoutingWordBudget
  gcongr

omit [Fintype V] in
/-- Replay the entire late phase using list-backed routing for both hub orientations. -/
def lateSteinerWithListHubWorkUsing (arcs : {r : List (V × V) // r.Nodup}) (n τ : ℕ)
    (vertices : List V) (sample : Finset V) (round : List (V × V) → Arcs V × ℕ)
    (D : List (V × V)) : Arcs V × ℕ :=
  let traces := lateHubTraceWithWordWorkFrom arcs n vertices sample D ⟨[],[],[]⟩
  let thick := anyThickRequestWithIntervalRowsWork arcs n τ traces.1.thin
  let preliminary := traces.2+thick.2+20
  if thick.1 then (⟨(arcs.val : Multiset (V × V)),arcs.property⟩,preliminary)
  else
    let hubs := hubPreserverListWithWordWork arcs n vertices sample traces.1.hits
    let rounding := round traces.1.thin
    let selected := unionRowsWithWordWork hubs.1 rounding.1
    (selected.1,preliminary+hubs.2+rounding.2+selected.2)

theorem lateSteinerWithListHubWorkUsing_spec (arcs : {r : List (V × V) // r.Nodup}) (τ : ℕ)
    (vertices : List V) (simple : vertices.Nodup) (complete : ∀ v : V, v ∈ vertices)
    (sample : Finset V) (early : EarlySteinerRule arcs.val.toFinset)
    (round : List (V × V) → Arcs V × ℕ) (D : List (V × V)) (budget : ℕ → ℕ) (mono : Monotone budget)
    (roundWork : ∀ T, (∀ d ∈ T, Reach arcs.val.toFinset d.1 d.2) → (round T).2 ≤ budget T.length)
    (feasible : ∀ d ∈ D, Reach arcs.val.toFinset d.1 d.2) :
    let n := Fintype.card V
    let traces := steinerPhaseTraces early 0 sample D
    let out := lateSteinerWithListHubWorkUsing arcs n τ vertices sample round D
    out.1 = (if traces.thin.any (fun d => decide (τ < (reachInterval arcs.val.toFinset d).card)) then arcs.val.toFinset
      else hubPreserver arcs.val.toFinset sample traces.hits ∪ (round traces.thin).1) ∧
      out.2 ≤ lateHubRoutingWordBudget n arcs.val.length D.length+budget D.length := by
  let n := Fintype.card V
  let m := arcs.val.length
  let p := D.length
  let st : SteinerPhaseTraces V := ⟨[],[],[]⟩
  let traces := lateHubTraceWithWordWorkFrom arcs n vertices sample D st
  let thick := anyThickRequestWithIntervalRowsWork arcs n τ traces.1.thin
  let hubs := hubPreserverListWithWordWork arcs n vertices sample traces.1.hits
  let combined := unionRowsWithWordWork hubs.1 (round traces.1.thin).1
  obtain ⟨raw,hits,thins,covered,pre⟩ :=
    lateHubTraceWithWordWorkFrom_spec arcs vertices simple complete sample early D st p (by simp [st,p]) (by simp [st,p])
  change traces.1 = steinerPhaseTraces early 0 sample D at raw
  change traces.1.hits.length ≤ p at hits
  change traces.1.thin.length ≤ p at thins
  change traces.2 ≤ p*(lateHubStepWordBudget n m p+8)+2 at pre
  obtain ⟨checked,checkWork⟩ := anyThickRequestWithIntervalRowsWork_spec arcs τ traces.1.thin
  obtain ⟨simpleHub,hubExact,hubWork⟩ :=
    hubPreserverListWithWordWork_spec arcs vertices simple complete sample traces.1.hits
  obtain ⟨combinedEq,combinedWork⟩ := unionRowsWithWordWork_spec hubs.1 (round traces.1.thin).1
  have supplied : ∀ d ∈ traces.1.thin, Reach arcs.val.toFinset d.1 d.2 := by
    intro d h
    exact feasible d ((covered d h).resolve_left (by simp [st]))
  have routeCap : hubs.2 ≤ p*(hitHubFromArcRowsWordBudget n m+11)+hubRouteListWordBudget n m p+8 := by
    have mon := hubRouteListWordBudget_mono n m hits
    exact hubWork.trans (by gcongr)
  have size : hubs.1.length ≤ n^2 := by
    change hubs.1.Nodup at simpleHub
    rw [← List.toFinset_card_of_nodup simpleHub,pow_two,← show Fintype.card (V × V) = n*n by simp [n]]
    exact card_le_univ _
  have count : combined.2 ≤ n^2*(12*n^2+16)+2 := by
    have product : Fintype.card (V × V) = n^2 := by simp [n,pow_two]
    exact combinedWork.trans (by rw [product]; gcongr)
  have thickCap : thick.2 ≤ p*(demandIntervalRowsWordBudget n m+n+8)+2 := checkWork.trans (by gcongr)
  have rounds := (roundWork traces.1.thin supplied).trans (mono thins)
  have main := Nat.add_le_add pre thickCap
  let initial : Arcs V := ⟨(arcs.val : Multiset (V × V)),arcs.property⟩
  have original : initial = arcs.val.toFinset := by
    ext e
    change e ∈ (arcs.val : Multiset (V × V)) ↔ e ∈ arcs.val.toFinset
    simp
  change (let out := if thick.1 then (initial,traces.2+thick.2+20)
    else (combined.1,traces.2+thick.2+20+hubs.2+(round traces.1.thin).2+combined.2)
    out.1 = _ ∧ out.2 ≤ lateHubRoutingWordBudget n m p+budget p)
  rw [← raw]
  change thick.1 = _ at checked
  rw [← checked]
  split
  · refine ⟨original,?_⟩
    unfold lateHubRoutingWordBudget
    omega
  · change combined.1 = _ at combinedEq
    change hubs.1.toFinset = _ at hubExact
    refine ⟨combinedEq.trans (by rw [hubExact]),?_⟩
    unfold lateHubRoutingWordBudget
    omega

/-- Use the list-backed hub phase and the precomputed-threshold thin evaluator. -/
def lateSteinerWithListHubWork {n : ℕ} (G : Arcs (Fin n))
    (arcs : {r : List (Fin n × Fin n) // r.Nodup}) (τ m : ℕ) (vertices : List (Fin n)) (sample : Finset (Fin n))
    (rows : ThinThresholdList (Fin n)) (D : List (Fin n × Fin n)) : Arcs (Fin n) × ℕ :=
  lateSteinerWithListHubWorkUsing arcs n τ vertices sample (fun T =>
    let thin := thinRoundRunFromThresholdListWithIntervalWork G arcs m rows (thinRoundingFactor n τ) T
    (thin.1.1,thin.2+thin.1.2)) D

theorem lateSteinerWithListHubWork_spec {n : ℕ} {G : Arcs (Fin n)} (early : EarlySteinerRule G)
    (arcs : {r : List (Fin n × Fin n) // r.Nodup}) (arcsEq : arcs.val.toFinset = G) (τ m : ℕ) (hm : m = G.card)
    (vertices : List (Fin n)) (simple : vertices.Nodup) (complete : ∀ v : Fin n, v ∈ vertices) (sample : Finset (Fin n))
    (rows : ThinThresholdList (Fin n)) (edges : ∀ r ∈ rows.val, r.1 ∈ G) (count : rows.val.length ≤ m)
    (D : List (Fin n × Fin n)) (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    let traces := steinerPhaseTraces early 0 sample D
    let out := lateSteinerWithListHubWork G arcs τ m vertices sample rows D
    out.1 = (if traces.thin.any (fun d => decide (τ < (reachInterval G d).card)) then G
      else hubPreserver G sample traces.hits ∪ (thinRoundRunFromThresholdRows G m (thinRoundingFactor n τ) rows.val.toFinset traces.thin).1) ∧
      out.2 ≤ lateHubRoutingWordBudget n m D.length+
        (steinerThinIntervalWorkBound n m D.length+thinRoundThresholdSearchWorkPolynomial n m D.length) := by
  subst G
  let G := arcs.val.toFinset
  let factor := thinRoundingFactor n τ
  let round (T : List (Fin n × Fin n)) : Arcs (Fin n) × ℕ :=
    let thin := thinRoundRunFromThresholdListWithIntervalWork G arcs m rows factor T
    (thin.1.1,thin.2+thin.1.2)
  let traces := steinerPhaseTraces early 0 sample D
  let budget (p : ℕ) := steinerThinIntervalWorkBound n m p+thinRoundThresholdSearchWorkPolynomial n m p
  have mono : Monotone budget := by
    intro a b short
    unfold budget steinerThinIntervalWorkBound steinerThinResidualRouteWorkBound steinerStreamingThinWorkBound
      thinRoundThresholdSearchWorkPolynomial
    gcongr
  have bound (T : List (Fin n × Fin n)) (ok : ∀ d ∈ T, Reach G d.1 d.2) :
      (round T).2 ≤ budget T.length := by
    let thin := thinRoundRunFromThresholdListWithIntervalWork G arcs m rows factor T
    have measured := thinRoundRunFromThresholdListWithIntervalWork_bound G arcs rfl m hm rows edges count factor T ok
    have legacy : thin.1.2 ≤ thinRoundThresholdSearchWorkPolynomial n m T.length := by
      have same := thinRoundRunFromThresholdListWithIntervalWork_eq G arcs rfl m hm rows factor T
      change thin.1 = _ at same
      rw [same]
      simpa only [Fintype.card_fin] using thinRoundRunFromThresholdRows_search_bound G m hm factor
        rows.val.toFinset (fun r h => edges r (List.mem_toFinset.mp h)) T ok
    exact Nat.add_le_add measured legacy
  obtain ⟨shape,work⟩ := lateSteinerWithListHubWorkUsing_spec arcs τ vertices simple complete
    sample early round D budget mono bound feasible
  have arcCount : arcs.val.length = m := by rw [← List.toFinset_card_of_nodup arcs.property,hm]
  have exactRound : (round traces.thin).1 = (thinRoundRunFromThresholdRows G m factor rows.val.toFinset traces.thin).1 := by
    change (thinRoundRunFromThresholdListWithIntervalWork G arcs m rows factor traces.thin).1.1 = _
    exact congrArg Prod.fst (thinRoundRunFromThresholdListWithIntervalWork_eq G arcs rfl m hm rows factor traces.thin)
  refine ⟨?_,?_⟩
  · change (lateSteinerWithListHubWorkUsing arcs n τ vertices sample round D).1 =
      (if traces.thin.any (fun d => decide (τ < (reachInterval G d).card)) then G
      else hubPreserver G sample traces.hits ∪ (thinRoundRunFromThresholdRows G m factor rows.val.toFinset traces.thin).1)
    rw [← exactRound]
    simpa only [Fintype.card_fin] using shape
  · simpa only [lateSteinerWithListHubWork,arcCount,Fintype.card_fin] using work

/-- The list implementation picks exactly the graph of the earlier late phase. -/
theorem lateSteinerWithListHubWork_graph {n : ℕ} {G : Arcs (Fin n)} (early : EarlySteinerRule G)
    (arcs : {r : List (Fin n × Fin n) // r.Nodup}) (arcsEq : arcs.val.toFinset = G) (τ m : ℕ) (hm : m = G.card)
    (vertices : List (Fin n)) (simple : vertices.Nodup) (complete : ∀ v : Fin n, v ∈ vertices) (sample : Finset (Fin n))
    (rows : ThinThresholdList (Fin n)) (edges : ∀ r ∈ rows.val, r.1 ∈ G) (count : rows.val.length ≤ m)
    (D : List (Fin n × Fin n)) (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    (lateSteinerWithListHubWork G arcs τ m vertices sample rows D).1 =
      (lateSteinerWithStoredThinThresholds G τ m sample rows.val.toFinset D).1 := by
  have exactGraph := (lateSteinerWithListHubWork_spec early arcs arcsEq τ m hm vertices simple complete
    sample rows edges count D feasible).1
  have old := lateSteinerWithStoredThinThresholds_graph early τ m sample rows.val.toFinset D feasible
  exact exactGraph.trans (by simpa only [Fintype.card_fin] using old.symm)

/-- Use a prepared thin update cap and rounding factor during late replay. -/
def lateSteinerWithThinServiceWorkAtControls {n : ℕ} (G : Arcs (Fin n))
    (arcs : {r : List (Fin n × Fin n) // r.Nodup}) (τ m fuel factor : ℕ)
    (vertices : List (Fin n)) (sample : Finset (Fin n))
    (rows : ThinThresholdList (Fin n)) (D : List (Fin n × Fin n)) : Arcs (Fin n) × ℕ :=
  lateSteinerWithListHubWorkUsing arcs n τ vertices sample (fun T =>
    let thin := thinRoundRunFromThresholdListWithServiceWorkAtFuel G arcs m fuel rows factor T
    (thin.1.1,thin.2+thin.1.2)) D

/-- Run the same late phase while charging each thin service test on its
retained rounded arc list. -/
def lateSteinerWithThinServiceWork {n : ℕ} (G : Arcs (Fin n))
    (arcs : {r : List (Fin n × Fin n) // r.Nodup}) (τ m : ℕ) (vertices : List (Fin n)) (sample : Finset (Fin n))
    (rows : ThinThresholdList (Fin n)) (D : List (Fin n × Fin n)) : Arcs (Fin n) × ℕ :=
  lateSteinerWithListHubWorkUsing arcs n τ vertices sample (fun T =>
    let thin := thinRoundRunFromThresholdListWithServiceWork G arcs m rows (thinRoundingFactor n τ) T
    (thin.1.1,thin.2+thin.1.2)) D

theorem lateSteinerWithThinServiceWorkAtControls_eq {n : ℕ} (G : Arcs (Fin n))
    (arcs : {r : List (Fin n × Fin n) // r.Nodup}) (τ m fuel factor : ℕ)
    (exactFuel : fuel = m*(m.log2+1)+1) (exactFactor : factor = thinRoundingFactor n τ)
    (vertices : List (Fin n)) (sample : Finset (Fin n))
    (rows : ThinThresholdList (Fin n)) (D : List (Fin n × Fin n)) :
    lateSteinerWithThinServiceWorkAtControls G arcs τ m fuel factor vertices sample rows D =
      lateSteinerWithThinServiceWork G arcs τ m vertices sample rows D := by
  subst fuel factor
  rfl

/-- Classification, hub routing, and any thick fallback keep their earlier
result. The thin service work adds at most one rounded-list budget per request. -/
theorem lateSteinerWithThinServiceWork_compare {n : ℕ} {G : Arcs (Fin n)}
    (arcs : {r : List (Fin n × Fin n) // r.Nodup}) (arcsEq : arcs.val.toFinset = G) (τ m : ℕ)
    (vertices : List (Fin n)) (simple : vertices.Nodup) (complete : ∀ v : Fin n, v ∈ vertices)
    (sample : Finset (Fin n)) (early : EarlySteinerRule G)
    (rows : ThinThresholdList (Fin n)) (D : List (Fin n × Fin n)) :
    let out := lateSteinerWithThinServiceWork G arcs τ m vertices sample rows D
    let old := lateSteinerWithListHubWork G arcs τ m vertices sample rows D
    out.1 = old.1 ∧ out.2 ≤ old.2+D.length*thinRoundedServiceWordBudget n rows.val.length := by
  subst G
  let G := arcs.val.toFinset
  let traces := lateHubTraceWithWordWorkFrom arcs n vertices sample D ⟨[],[],[]⟩
  let thin := thinRoundRunFromThresholdListWithServiceWork G arcs m rows (thinRoundingFactor n τ) traces.1.thin
  let prior := thinRoundRunFromThresholdListWithIntervalWork G arcs m rows (thinRoundingFactor n τ) traces.1.thin
  have count : traces.1.thin.length ≤ D.length := by
    simpa only [Fintype.card_fin] using (lateHubTraceWithWordWorkFrom_spec arcs vertices simple complete sample
      early D ⟨[],[],[]⟩ D.length (by simp) (by simp)).2.2.1
  obtain ⟨same,cost⟩ := thinRoundRunFromThresholdListWithServiceWork_spec G arcs m rows
    (thinRoundingFactor n τ) traces.1.thin
  change thin.1 = prior.1 at same
  change thin.2 ≤ prior.2+traces.1.thin.length*thinRoundedServiceWordBudget n rows.val.length at cost
  have bound := cost.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ count) _)
  dsimp only [lateSteinerWithThinServiceWork,lateSteinerWithListHubWork,lateSteinerWithListHubWorkUsing]
  split
  · exact ⟨rfl,Nat.le_add_right _ _⟩
  · change (unionRowsWithWordWork _ thin.1.1).1 = (unionRowsWithWordWork _ prior.1.1).1 ∧
      _ + (thin.2+thin.1.2)+(unionRowsWithWordWork _ thin.1.1).2 ≤
        _ + (prior.2+prior.1.2)+(unionRowsWithWordWork _ prior.1.1).2 +
          D.length*thinRoundedServiceWordBudget n rows.val.length
    rw [same]
    exact ⟨rfl,by omega⟩

end OnlineReachabilityPreservers
