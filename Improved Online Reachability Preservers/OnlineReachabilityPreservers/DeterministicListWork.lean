import OnlineReachabilityPreservers.AlgorithmSearchWork

/-! Comparison work of list-backed deterministic graph operations. -/

namespace OnlineReachabilityPreservers

open Finset

/-- A membership scan returns the list membership decision and charges each tested key. -/
theorem memScanWithChecks_spec {A : Type*} [DecidableEq A] (a : A) (xs : List A) :
    (anyWithChecks (fun x => decide (a = x)) xs).1 = decide (a ∈ xs) ∧
      (anyWithChecks (fun x => decide (a = x)) xs).2 ≤ xs.length := by
  obtain ⟨found, cap⟩ := anyWithChecks_spec (fun x => decide (a=x)) xs
  refine ⟨found.trans ?_, cap⟩
  apply Bool.eq_iff_iff.mpr
  simp [List.any_eq_true]

variable {V : Type*} [LinearOrder V] [Fintype V]

/-- One unit for inspecting the list tag and one for running the key test
on a nonempty cell. The empty-cell inspection is also charged. -/
def anyScanWordSteps {A : Type*} (test : A → Bool) : List A → ℕ
  | [] => 1
  | a :: rest => if test a then 2 else 2 + anyScanWordSteps test rest

/-- The short-circuit scan count accounts for every inspected cell. -/
theorem anyScanWordSteps_eq {A : Type*} (test : A → Bool) (keys : List A) :
    let out := anyWithChecks test keys
    anyScanWordSteps test keys = 2 * out.2 + if out.1 then 0 else 1 := by
  change _ = 2 * (anyWithChecks test keys).2 + if (anyWithChecks test keys).1 then 0 else 1
  induction keys with
  | nil => rfl
  | cons a rest ih =>
    cases h : test a with
    | true => simp [anyScanWordSteps, anyWithChecks,h]
    | false =>
      simp only [anyScanWordSteps, anyWithChecks,h, Bool.false_eq_true,↓reduceIte,ih]
      omega

/-- Report the exact key membership with the list scan charge. -/
def memScanWithWordWork {A : Type*} [DecidableEq A] (key : A) (keys : List A) : Bool × ℕ :=
  let found := anyWithChecks (fun item => decide (key = item)) keys
  (found.1, 2 * found.2 + if found.1 then 0 else 1)

theorem memScanWithWordWork_spec {A : Type*} [DecidableEq A] (key : A) (keys : List A) :
    let out := memScanWithWordWork key keys
    out.1 = decide (key ∈ keys) ∧ out.2 ≤ 2 * keys.length + 1 := by
  obtain ⟨same, cost⟩ := memScanWithChecks_spec key keys
  refine ⟨same, ?_⟩
  change 2 * (anyWithChecks (fun item => decide (key = item)) keys).2 +
    (if (anyWithChecks (fun item => decide (key = item)) keys).1 then 0 else 1) ≤ 2 * keys.length + 1
  split <;> omega

omit [Fintype V] in
private def reverseSweepWithMeasure (countWords : Bool) (reachable : List V) :
    List (V × V) → List V → List V × ℕ
  | [], seen => (seen, if countWords then 1 else 0)
  | e :: arcs, seen =>
    let target := anyWithChecks (fun x => decide (e.2 = x)) reachable
    let source := anyWithChecks (fun x => decide (e.1 = x)) seen
    let result := reverseSweepWithMeasure countWords reachable arcs
      (if target.1 && !source.1 then e.1 :: seen else seen)
    if countWords then
      let targetSteps := 2 * target.2 + if target.1 then 0 else 1
      let sourceSteps := 2 * source.2 + if source.1 then 0 else 1
      (result.1, 12 + targetSteps + sourceSteps + result.2)
    else (result.1, target.2 + source.2 + result.2)

omit [Fintype V] in
private def reverseSweepWithChecks (reachable : List V) : List (V × V) → List V → List V × ℕ :=
  reverseSweepWithMeasure false reachable

omit [Fintype V] in
private def reverseSweepWithWordWork (reachable : List V) : List (V × V) → List V → List V × ℕ :=
  reverseSweepWithMeasure true reachable

omit [Fintype V] in
private theorem prependOrKeep_spec (seen : List V) (u : V) (yes : Prop) [Decidable yes]
    (simple : seen.Nodup) :
    let next := if decide yes && !(decide (u ∈ seen)) then u::seen else seen
    next.Nodup ∧ ∀ v, v ∈ next ↔ v ∈ seen ∨ v = u ∧ yes := by
  by_cases hx : u ∈ seen
  · simp only [hx, decide_true, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    exact ⟨simple, fun v => ⟨Or.inl, fun h => h.elim id (fun hc => hc.1.symm ▸ hx)⟩⟩
  · by_cases h : yes
    · simp [hx, h, simple, or_comm]
    · simp [hx, h, simple]

private theorem reverseSweepWithChecks_spec (reachable : List V) (arcs : List (V × V))
    (seen : List V) (simple : seen.Nodup) :
    let out := reverseSweepWithChecks reachable arcs seen
    out.1.Nodup ∧
      (∀ v, v ∈ out.1 ↔ v ∈ seen ∨ ∃ w, (v,w) ∈ arcs ∧ w ∈ reachable) ∧
      out.2 ≤ arcs.length * (reachable.length + Fintype.card V) := by
  induction arcs generalizing seen with
  | nil => simp [reverseSweepWithChecks, reverseSweepWithMeasure, simple]
  | cons e arcs ih =>
    obtain ⟨target, targetCost⟩ := memScanWithChecks_spec e.2 reachable
    obtain ⟨source, sourceCost⟩ := memScanWithChecks_spec e.1 seen
    let next := if decide (e.2 ∈ reachable) && !(decide (e.1 ∈ seen)) then e.1::seen else seen
    have prepared : next.Nodup ∧ ∀ v, v ∈ next ↔ v ∈ seen ∨ v = e.1 ∧ e.2 ∈ reachable :=
      prependOrKeep_spec seen e.1 (e.2 ∈ reachable) simple
    obtain ⟨finalSimple, membership, count⟩ := ih next prepared.1
    simp only [reverseSweepWithChecks, reverseSweepWithMeasure, target, source, Bool.false_eq_true, ↓reduceIte]
    use finalSimple
    constructor
    · intro v
      change v ∈ (reverseSweepWithChecks reachable arcs next).1 ↔ _
      rw [membership, prepared.2]
      rcases e with ⟨a,b⟩
      simp only [List.mem_cons, Prod.mk.injEq]
      constructor
      · rintro ((h | ⟨rfl,h⟩) | ⟨w, hArc, hReach⟩)
        · exact Or.inl h
        · exact Or.inr ⟨b, Or.inl ⟨rfl,rfl⟩,h⟩
        · exact Or.inr ⟨w, Or.inr hArc,hReach⟩
      · rintro (h | ⟨w,(⟨rfl,rfl⟩ | hArc),hReach⟩)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr ⟨rfl,hReach⟩)
        · exact Or.inr ⟨w,hArc,hReach⟩
    · have seenSize : seen.length ≤ Fintype.card V := by
        rw [← List.toFinset_card_of_nodup simple]
        exact card_le_univ _
      have budget := Nat.add_le_add (Nat.add_le_add targetCost (sourceCost.trans seenSize)) count
      simpa only [next, reverseSweepWithChecks, List.length_cons, Nat.succ_mul, add_comm] using budget

/-- Compare list keys in every reverse-search membership test, including
insertion into the set of discovered vertices. -/
def reachInListWithChecks (arcs : List (V × V)) (t : V) : ℕ → List V × ℕ
  | 0 => ([t],0)
  | k+1 =>
    let prior := reachInListWithChecks arcs t k
    let sweep := reverseSweepWithChecks prior.1 arcs prior.1
    (sweep.1, prior.2 + sweep.2)

/-- Reverse reachability in the same list representation, with charges for
loop control, list-cell inspection and construction, and key comparisons.
A composite key test counts as one operation. Counter maintenance is
excluded from this source-level tally. -/
def reachInListWithWordWork (arcs : List (V × V)) (t : V) : ℕ → List V × ℕ
  | 0 => ([t], 2)
  | k+1 =>
    let prior := reachInListWithWordWork arcs t k
    let sweep := reverseSweepWithWordWork prior.1 arcs prior.1
    (sweep.1, 4 + prior.2 + sweep.2)

theorem reachInListWithChecks_spec (arcs : List (V × V)) (t : V) (k : ℕ) :
    let out := reachInListWithChecks arcs t k
    out.1.Nodup ∧ out.1.toFinset = reachIn arcs.toFinset t k ∧
      out.2 ≤ k * (arcs.length * (2 * Fintype.card V)) := by
  induction k with
  | zero => simp [reachInListWithChecks, reachIn]
  | succ k ih =>
    let prior := reachInListWithChecks arcs t k
    obtain ⟨simple, correct, earlier⟩ := ih
    change prior.1.Nodup at simple
    change prior.1.toFinset = _ at correct
    change prior.2 ≤ _ at earlier
    obtain ⟨nextSimple, membership, work⟩ := reverseSweepWithChecks_spec prior.1 arcs prior.1 simple
    simp only [reachInListWithChecks]
    refine ⟨nextSimple, ?_, ?_⟩
    · ext v
      simp only [List.mem_toFinset, reachIn_succ]
      rw [membership]
      simp only [← correct, List.mem_toFinset, Edge]
    · have priorSize : prior.1.length ≤ Fintype.card V := by
        rw [← List.toFinset_card_of_nodup simple]
        exact card_le_univ _
      have thisSweep : (reverseSweepWithChecks prior.1 arcs prior.1).2 ≤ arcs.length*(2*Fintype.card V) :=
        work.trans (Nat.mul_le_mul_left _ (by omega))
      exact (Nat.add_le_add earlier thisSweep).trans_eq ((Nat.succ_mul _ _).symm)

omit [Fintype V] in
private theorem least?_insert_key (S : Finset V) (v : V) :
    least? (insert v S) = some ((least? S).elim v (min v)) := by
  cases old : least? S with
  | none =>
    have sEmpty := least?_eq_none.mp old
    simp [sEmpty, least?]
  | some best =>
    obtain ⟨next, found⟩ := least?_some (insert_nonempty v S)
    rw [found]
    apply congrArg some
    have oldMem := least?_mem old
    have minimumMem : min v best ∈ insert v S := by
      by_cases order : v ≤ best
      · simp [min_eq_left order]
      · simp [min_eq_right (le_of_not_ge order), oldMem]
    apply le_antisymm (least?_le found minimumMem)
    rcases mem_insert.mp (least?_mem found) with first | first
    · rw [first]
      exact min_le_left _ _
    · exact (min_le_right _ _).trans (least?_le old first)

omit [Fintype V] in
/-- Find the least accepted candidate, adding one charge per minimum call. -/
def leastWhereWithChecks (test : V → Bool × ℕ) : List V → Option V × ℕ
  | [] => (none, 0)
  | v::rest =>
    let checked := test v
    let tail := leastWhereWithChecks test rest
    if checked.1 then
      match tail.1 with
      | none => (some v, checked.2 + tail.2)
      | some best => (some (min v best), checked.2 + tail.2 + 1)
    else (tail.1, checked.2 + tail.2)

omit [Fintype V] in
/-- The least candidate and the charge for testing every candidate and comparing minima. -/
theorem leastWhereWithChecks_spec (test : V → Bool × ℕ) (P : V → Prop) [DecidablePred P]
    (candidates : List V) (budget : ℕ)
    (passes : ∀ v ∈ candidates, (test v).1 = decide (P v))
    (testCost : ∀ v ∈ candidates, (test v).2 ≤ budget) :
    let out := leastWhereWithChecks test candidates
    out.1 = least? (candidates.toFinset.filter P) ∧ out.2 ≤ candidates.length * (budget+1) := by
  induction candidates with
  | nil => simp [leastWhereWithChecks, least?]
  | cons v rest ih =>
    let tail := leastWhereWithChecks test rest
    let checked := test v
    obtain ⟨found, work⟩ := ih
      (fun w hw => passes w (List.mem_cons_of_mem _ hw))
      (fun w hw => testCost w (List.mem_cons_of_mem _ hw))
    change tail.1 = _ at found
    change tail.2 ≤ _ at work
    have accepted : checked.1 = decide (P v) := passes v List.mem_cons_self
    have charged : checked.2 ≤ budget := testCost v List.mem_cons_self
    let step := if checked.1 then
      match tail.1 with
      | none => (some v, checked.2+tail.2)
      | some best => (some (min v best), checked.2+tail.2+1)
      else (tail.1,checked.2+tail.2)
    change step.1 = least? ((v::rest).toFinset.filter P) ∧ step.2 ≤ (rest.length+1)*(budget+1)
    have cap : checked.2 + tail.2 + 1 ≤ (rest.length+1)*(budget+1) := by
      rw [Nat.succ_mul]
      omega
    by_cases present : P v
    · have filterEq : ((v::rest).toFinset.filter P) = insert v (rest.toFinset.filter P) := by
        simp only [List.toFinset_cons, filter_insert, present, ↓reduceIte]
      have eq : checked.1 = true := by simpa only [present, decide_true] using accepted
      rw [filterEq, least?_insert_key, ← found]
      cases result : tail.1 with
      | none =>
        simp only [step, eq, ↓reduceIte, result, Option.elim_none, true_and]
        exact (Nat.le_succ _).trans cap
      | some best =>
        simp only [step, eq, ↓reduceIte, result, Option.elim_some, true_and]
        exact cap
    · have filterEq : ((v::rest).toFinset.filter P) = rest.toFinset.filter P := by
        simp only [List.toFinset_cons, filter_insert, present, ↓reduceIte]
      have eq : checked.1 = false := by simpa only [present, decide_false] using accepted
      rw [filterEq]
      simp only [step, eq, Bool.false_eq_true, ↓reduceIte]
      exact ⟨found, (Nat.le_succ _).trans cap⟩

omit [Fintype V] in
def leastSuccessorWithChecks (arcs : List (V × V)) (u : V) (candidates : List V) : Option V × ℕ :=
  leastWhereWithChecks (fun v => anyWithChecks (fun a => decide ((u,v) = a)) arcs) candidates

omit [Fintype V] in
theorem leastSuccessorWithChecks_spec (arcs : List (V × V)) (u : V) (candidates : List V) :
    let out := leastSuccessorWithChecks arcs u candidates
    out.1 = least? (candidates.toFinset.filter (Edge arcs.toFinset u)) ∧
      out.2 ≤ candidates.length * (arcs.length+1) := by
  apply leastWhereWithChecks_spec
  · intro v _
    have found := (memScanWithChecks_spec (u,v) arcs).1
    rw [found]
    exact Bool.eq_iff_iff.mpr (by simp [Edge])
  · intro v _
    exact (memScanWithChecks_spec (u,v) arcs).2

omit [Fintype V] in
private def nextVertexListWithChecks (G H : List (V × V)) (R : List V) (u : V) : Option V × ℕ :=
  let old := leastSuccessorWithChecks H u R
  let new := leastSuccessorWithChecks G u R
  (old.1.or new.1, old.2+new.2)

omit [Fintype V] in
private theorem nextVertexListWithChecks_spec (G H : List (V × V)) (R : List V) (u : V) :
    let out := nextVertexListWithChecks G H R u
    out.1 = nextVertex G.toFinset H.toFinset R.toFinset u ∧
      out.2 ≤ R.length*(G.length+H.length+2) := by
  obtain ⟨old, workOld⟩ := leastSuccessorWithChecks_spec H u R
  obtain ⟨new, workNew⟩ := leastSuccessorWithChecks_spec G u R
  simp only [nextVertexListWithChecks, old, new, nextVertex, true_and]
  exact (Nat.add_le_add workOld workNew).trans_eq (by ring)

omit [Fintype V] in
private def growListWithWork (successor : V → Option V × ℕ) (baseCharge stepCharge : ℕ) (t : V) :
    ℕ → V → Option (List (V × V)) × ℕ
  | 0, u => (if u = t then some [] else none, baseCharge)
  | k+1, u =>
    if u = t then (some [], baseCharge)
    else
      let next := successor u
      match next.1 with
      | none => (none, stepCharge+next.2)
      | some v =>
        let rest := growListWithWork successor baseCharge stepCharge t k v
        (rest.1.map ((u,v)::·), stepCharge+next.2+rest.2)

omit [Fintype V] in
private theorem growListWithWork_spec (G H : List (V × V)) (R : List V)
    (successor : V → Option V × ℕ) (baseCharge stepCharge bound : ℕ) (t : V) (k : ℕ) (u : V)
    (baseLe : baseCharge ≤ stepCharge + bound)
    (successorSpec : ∀ v, (successor v).1 = nextVertex G.toFinset H.toFinset R.toFinset v ∧
      (successor v).2 ≤ bound) :
    let out := growListWithWork successor baseCharge stepCharge t k u
    out.1 = growFrom G.toFinset H.toFinset R.toFinset t k u ∧
      out.2 ≤ (k+1)*(stepCharge+bound) ∧
      (out.1.getD []).length ≤ k := by
  induction k generalizing u with
  | zero =>
    by_cases same : u = t <;> simpa [growListWithWork, growFrom, same] using baseLe
  | succ k ih =>
    have product : stepCharge+bound ≤ (k+1+1)*(stepCharge+bound) := Nat.le_mul_of_pos_left _ (by omega)
    by_cases same : u = t
    · have cap := baseLe.trans product
      simpa [growListWithWork, growFrom, same] using cap
    obtain ⟨answers, calls⟩ := successorSpec u
    let next := successor u
    change next.1 = _ at answers
    change next.2 ≤ bound at calls
    cases picked : next.1 with
    | none =>
      have missing := answers.symm.trans picked
      have out : growListWithWork successor baseCharge stepCharge t (k+1) u = (none, stepCharge+next.2) := by
        rw [growListWithWork, ite_eq_right same]
        change (match next.1 with | none => _ | some v => _) = _
        rw [picked]
      have path : growFrom G.toFinset H.toFinset R.toFinset t (k+1) u = none := by
        simp [growFrom, same, missing]
      rw [out, path]
      exact ⟨rfl, (Nat.add_le_add_left calls _).trans product, Nat.zero_le _⟩
    | some v =>
      have found := answers.symm.trans picked
      obtain ⟨result, checks, length⟩ := ih v
      let rest := growListWithWork successor baseCharge stepCharge t k v
      change rest.1 = _ at result
      change rest.2 ≤ (k+1)*(stepCharge+bound) at checks
      change (rest.1.getD []).length ≤ k at length
      have needed : stepCharge+next.2+rest.2 ≤ (k+1+1)*(stepCharge+bound) := by
        rw [Nat.succ_mul]
        omega
      have out : growListWithWork successor baseCharge stepCharge t (k+1) u =
          (rest.1.map ((u,v)::·), stepCharge+next.2+rest.2) := by
        rw [growListWithWork, ite_eq_right same]
        change (match next.1 with | none => _ | some v => _) = _
        rw [picked]
      have path : growFrom G.toFinset H.toFinset R.toFinset t (k+1) u =
          (growFrom G.toFinset H.toFinset R.toFinset t k v).map ((u,v)::·) := by
        simp only [growFrom, same, ↓reduceIte, found]
        change (growFrom G.toFinset H.toFinset R.toFinset t k v).bind
          (fun tail => some ((u,v)::tail)) = _
        cases growFrom G.toFinset H.toFinset R.toFinset t k v <;> rfl
      rw [out, path, ← result]
      refine ⟨rfl, needed, ?_⟩
      cases got : rest.1 with
      | none => simp
      | some path =>
        simpa only [got, Option.map_some, Option.getD_some, List.length_cons] using
          Nat.succ_le_succ (show path.length ≤ k by simpa only [got, Option.getD_some] using length)

omit [Fintype V] in
private def growListWithChecks (G H : List (V × V)) (R : List V) (t : V) :
    ℕ → V → Option (List (V × V)) × ℕ :=
  growListWithWork (nextVertexListWithChecks G H R) 1 1 t

omit [Fintype V] in
private theorem growListWithChecks_spec (G H : List (V × V)) (R : List V) (t : V) (k : ℕ) (u : V) :
    let out := growListWithChecks G H R t k u
    out.1 = growFrom G.toFinset H.toFinset R.toFinset t k u ∧
      out.2 ≤ (k+1)*(1+R.length*(G.length+H.length+2)) ∧
      (out.1.getD []).length ≤ k :=
  growListWithWork_spec G H R _ 1 1 _ t k u (Nat.le_add_right _ _) (nextVertexListWithChecks_spec G H R)

/-- Run both deterministic path searches with list-backed graph and vertex sets.
Every vertex or edge-key comparison in these searches is counted. -/
def forwardPathListWithChecks (G H : List (V × V)) (s t : V) : Option (List (V × V)) × ℕ :=
  let n := Fintype.card V
  let reach := reachInListWithChecks G t n
  let path := growListWithChecks G H reach.1 t n s
  (path.1, reach.2+path.2)

theorem forwardPathListWithChecks_spec (G H : List (V × V)) (s t : V) :
    let n := Fintype.card V
    let out := forwardPathListWithChecks G H s t
    out.1 = forwardPath G.toFinset H.toFinset s t ∧
      out.2 ≤ n*(G.length*(2*n)) + (n+1)*(1+n*(G.length+H.length+2)) ∧
      (out.1.getD []).length ≤ n := by
  let n := Fintype.card V
  let reach := reachInListWithChecks G t n
  obtain ⟨simple, correct, reverseCost⟩ := reachInListWithChecks_spec G t n
  change reach.1.Nodup at simple
  change reach.1.toFinset = reachIn G.toFinset t n at correct
  change reach.2 ≤ _ at reverseCost
  have reachSize : reach.1.length ≤ n := by
    rw [← List.toFinset_card_of_nodup simple]
    exact card_le_univ _
  obtain ⟨same, forwardCost, length⟩ := growListWithChecks_spec G H reach.1 t n s
  refine ⟨same.trans ?_, Nat.add_le_add reverseCost (forwardCost.trans ?_), length⟩
  · rw [correct]
    rfl
  · gcongr

/-- Insert list keys into a set represented by a duplicate-free list, charging membership tests. -/
def insertListWithChecks {A : Type*} [DecidableEq A] : List A → List A → List A × ℕ
  | [], seen => (seen, 0)
  | a::as, seen =>
    let present := anyWithChecks (fun x => decide (a=x)) seen
    let out := insertListWithChecks as (if present.1 then seen else a::seen)
    (out.1,present.2+out.2)

/-- The list union stays duplicate-free and charges at most one scan per inserted key. -/
theorem insertListWithChecks_spec {A : Type*} [DecidableEq A] [Fintype A]
    (xs seen : List A) (simple : seen.Nodup) :
    let out := insertListWithChecks xs seen
    out.1.Nodup ∧ out.1.toFinset = seen.toFinset ∪ xs.toFinset ∧
      out.2 ≤ xs.length*Fintype.card A := by
  induction xs generalizing seen with
  | nil => simp [insertListWithChecks, simple]
  | cons x xs ih =>
    let present := anyWithChecks (fun y => decide (x=y)) seen
    obtain ⟨member, work⟩ := memScanWithChecks_spec x seen
    let next := if present.1 then seen else x::seen
    have nextSimple : next.Nodup := by
      change (if present.1 then seen else x::seen).Nodup
      change present.1 = decide (x ∈ seen) at member
      rw [member]
      by_cases h : x ∈ seen <;> simp [h, simple]
    have insertEq : next.toFinset = insert x seen.toFinset := by
      change (if present.1 then seen else x::seen).toFinset = _
      rw [member]
      by_cases h : x ∈ seen
      · simp [h]
      · simp [h]
    obtain ⟨finalSimple, union, cost⟩ := ih next nextSimple
    refine ⟨finalSimple, ?_, ?_⟩
    · change (insertListWithChecks xs next).1.toFinset = _
      rw [union, insertEq, List.toFinset_cons, insert_union, union_insert]
    · have size : seen.length ≤ Fintype.card A := by
        rw [← List.toFinset_card_of_nodup simple]
        exact card_le_univ _
      change present.2 + (insertListWithChecks xs next).2 ≤ (xs.length+1)*Fintype.card A
      exact (Nat.add_le_add (work.trans size) cost).trans_eq (by rw [Nat.succ_mul]; ac_rfl)

private def forwardStepListWithChecks (G H : List (V × V)) (d : V × V) : List (V × V) × ℕ :=
  let searched := forwardPathListWithChecks G H d.1 d.2
  let inserted := insertListWithChecks (searched.1.getD []) H
  (inserted.1, searched.2+inserted.2)

/-- An explicit comparison bound per arrival for n vertices and an input
arc list of length m. A pair equality is one key comparison. -/
def forwardStepListBudget (n m : ℕ) : ℕ :=
  n*(m*(2*n)) + (n+1)*(1+n*(m+n^2+2)) + n*n^2

private theorem forwardStepListWithChecks_spec (G H : List (V × V)) (d : V × V) (simple : H.Nodup) :
    let out := forwardStepListWithChecks G H d
    out.1.Nodup ∧ out.1.toFinset = forwardStep G.toFinset H.toFinset d ∧
      out.2 ≤ forwardStepListBudget (Fintype.card V) G.length := by
  obtain ⟨same, cost, length⟩ := forwardPathListWithChecks_spec G H d.1 d.2
  let searched := forwardPathListWithChecks G H d.1 d.2
  have size : H.length ≤ Fintype.card V ^ 2 := by
    rw [← List.toFinset_card_of_nodup simple, pow_two, ← Fintype.card_prod]
    exact card_le_univ _
  have pathWork : searched.2 ≤ Fintype.card V*(G.length*(2*Fintype.card V)) +
      (Fintype.card V+1)*(1+Fintype.card V*(G.length+Fintype.card V^2+2)) :=
    cost.trans (by gcongr)
  obtain ⟨afterSimple, updated, addCost⟩ := insertListWithChecks_spec (searched.1.getD []) H simple
  have additions : (insertListWithChecks (searched.1.getD []) H).2 ≤ Fintype.card V * Fintype.card V ^ 2 := by
    apply addCost.trans
    rw [Fintype.card_prod, ← pow_two]
    exact Nat.mul_le_mul_right _ length
  refine ⟨afterSimple, ?_, Nat.add_le_add pathWork additions⟩
  change (insertListWithChecks (searched.1.getD []) H).1.toFinset = _
  rw [updated, forwardStep, forwardEdges]
  change searched.1 = _ at same
  rw [same]

/-- Count key comparisons in deterministic path growth and updates of the
preserver, using a list of input arcs. -/
def forwardRunListWithChecks (G : List (V × V)) : List (V × V) → List (V × V) → List (V × V) × ℕ
  | [], H => (H,0)
  | d::D, H =>
    let step := forwardStepListWithChecks G H d
    let final := forwardRunListWithChecks G D step.1
    (final.1, step.2+final.2)

/-- The metered list evaluator has the ordinary forward run's edge set after
every prefix. The bound includes reverse search, priority tests, and purchase. -/
theorem forwardRunListWithChecks_spec (G D H : List (V × V)) (simple : H.Nodup) :
    let out := forwardRunListWithChecks G D H
    out.1.Nodup ∧ out.1.toFinset = forwardRunFrom G.toFinset H.toFinset D ∧
      out.2 ≤ D.length * forwardStepListBudget (Fintype.card V) G.length := by
  induction D generalizing H with
  | nil => simp [forwardRunListWithChecks, forwardRunFrom, simple]
  | cons d D ih =>
    let step := forwardStepListWithChecks G H d
    obtain ⟨simpleStep, same, cost⟩ := forwardStepListWithChecks_spec G H d simple
    obtain ⟨finalSimple, exactRun, work⟩ := ih step.1 simpleStep
    refine ⟨finalSimple, ?_, (Nat.add_le_add cost work).trans_eq (by rw [List.length_cons, Nat.succ_mul]; ac_rfl)⟩
    change (forwardRunListWithChecks G D step.1).1.toFinset = _
    change step.1.toFinset = _ at same
    rw [exactRun, same]
    rfl

/-- Test one vertex against a bounded reverse search, counting all key comparisons. -/
def reachTestListWithChecks (arcs : List (V × V)) (s t : V) (depth : ℕ) : Bool × ℕ :=
  let found := reachInListWithChecks arcs t depth
  let member := anyWithChecks (fun v => decide (s = v)) found.1
  (member.1,found.2+member.2)

theorem reachTestListWithChecks_spec (arcs : List (V × V)) (s t : V) (depth : ℕ) :
    let n := Fintype.card V
    let out := reachTestListWithChecks arcs s t depth
    out.1 = decide (s ∈ reachIn arcs.toFinset t depth) ∧
      out.2 ≤ depth*(arcs.length*(2*n))+n := by
  let found := reachInListWithChecks arcs t depth
  obtain ⟨distinct, reached, work⟩ := reachInListWithChecks_spec arcs t depth
  obtain ⟨member, cost⟩ := memScanWithChecks_spec s found.1
  have size : found.1.length ≤ Fintype.card V := by
    rw [← List.toFinset_card_of_nodup distinct]
    exact card_le_univ _
  refine ⟨?_, Nat.add_le_add work (cost.trans size)⟩
  change (anyWithChecks _ found.1).1 = _
  rw [member]
  have reachedEq : found.1.toFinset = reachIn arcs.toFinset t depth := reached
  rw [← reachedEq]
  simp only [List.mem_toFinset]

omit [Fintype V] in
private theorem reverseSweepWithWordWork_spec (reachable : List V) (arcs : List (V × V))
    (seen : List V) :
    let measured := reverseSweepWithWordWork reachable arcs seen
    let checked := reverseSweepWithChecks reachable arcs seen
    measured.1 = checked.1 ∧ measured.2 ≤ 1 + 14 * arcs.length + 2 * checked.2 := by
  change (reverseSweepWithWordWork reachable arcs seen).1 = (reverseSweepWithChecks reachable arcs seen).1 ∧
    (reverseSweepWithWordWork reachable arcs seen).2 ≤ 1 + 14 * arcs.length + 2 * (reverseSweepWithChecks reachable arcs seen).2
  induction arcs generalizing seen with
  | nil => simp [reverseSweepWithWordWork, reverseSweepWithChecks, reverseSweepWithMeasure]
  | cons e rest ih =>
    let target := anyWithChecks (fun x => decide (e.2 = x)) reachable
    let source := anyWithChecks (fun x => decide (e.1 = x)) seen
    let next := if target.1 && !source.1 then e.1 :: seen else seen
    obtain ⟨same,tail⟩ := ih next
    have targetTicks : (if target.1 then 0 else 1) ≤ (1 : ℕ) := by split <;> decide
    have sourceTicks : (if source.1 then 0 else 1) ≤ (1 : ℕ) := by split <;> decide
    refine ⟨same,?_⟩
    change 12 + (2*target.2 + if target.1 then 0 else 1) +
      (2*source.2 + if source.1 then 0 else 1) + (reverseSweepWithWordWork reachable rest next).2 ≤
      1 + 14*(rest.length+1) + 2*(target.2 + source.2 + (reverseSweepWithChecks reachable rest next).2)
    omega

omit [Fintype V] in
private theorem reachInListWithWordWork_compares (arcs : List (V × V)) (t : V) (depth : ℕ) :
    let measured := reachInListWithWordWork arcs t depth
    let checked := reachInListWithChecks arcs t depth
    measured.1 = checked.1 ∧ measured.2 ≤ 2 + depth * (5 + 14 * arcs.length) + 2 * checked.2 := by
  change (reachInListWithWordWork arcs t depth).1 = (reachInListWithChecks arcs t depth).1 ∧
    (reachInListWithWordWork arcs t depth).2 ≤ 2 + depth * (5 + 14 * arcs.length) + 2 * (reachInListWithChecks arcs t depth).2
  induction depth with
  | zero => simp [reachInListWithWordWork, reachInListWithChecks]
  | succ k ih =>
    let measured := reachInListWithWordWork arcs t k
    let checked := reachInListWithChecks arcs t k
    obtain ⟨same,work⟩ := ih
    change measured.1 = checked.1 at same
    change measured.2 ≤ 2 + k*(5+14*arcs.length) + 2*checked.2 at work
    obtain ⟨reach,sweep⟩ := reverseSweepWithWordWork_spec checked.1 arcs checked.1
    refine ⟨?_,?_⟩
    · change (reverseSweepWithWordWork measured.1 arcs measured.1).1 = _
      rw [same]
      exact reach
    · change 4 + measured.2 + (reverseSweepWithWordWork measured.1 arcs measured.1).2 ≤
        2 + (k+1)*(5+14*arcs.length) + 2*(checked.2+(reverseSweepWithChecks checked.1 arcs checked.1).2)
      rw [same, Nat.succ_mul]
      omega

/-- Reverse search to the vertex count, in the source-level tally. -/
def reachInListWordBudget (n m : ℕ) : ℕ := 2 + n * (5 + m * (14 + 4 * n))

/-- The metered reverse-search loop returns the same reachable set with an
explicit polynomial word-operation bound for any requested depth. -/
theorem reachInListWithWordWork_spec (arcs : List (V × V)) (t : V) (depth : ℕ) :
    let out := reachInListWithWordWork arcs t depth
    out.1.Nodup ∧ out.1.toFinset = reachIn arcs.toFinset t depth ∧
      out.2 ≤ 2 + depth * (5 + arcs.length * (14 + 4 * Fintype.card V)) := by
  obtain ⟨same,extra⟩ := reachInListWithWordWork_compares arcs t depth
  obtain ⟨simple,reached,checks⟩ := reachInListWithChecks_spec arcs t depth
  refine ⟨same.symm ▸ simple, same.symm ▸ reached, ?_⟩
  exact extra.trans ((Nat.add_le_add_left (Nat.mul_le_mul_left 2 checks) _).trans_eq (by ring))

omit [Fintype V] in
def leastSuccessorWithWordWork (arcs : List (V × V)) (u : V) (candidates : List V) : Option V × ℕ :=
  let found := leastWhereWithChecks (fun v => memScanWithWordWork (u,v) arcs) candidates
  (found.1, found.2+8*candidates.length+1)

omit [Fintype V] in
theorem leastSuccessorWithWordWork_spec (arcs : List (V × V)) (u : V) (candidates : List V) :
    let out := leastSuccessorWithWordWork arcs u candidates
    out.1 = least? (candidates.toFinset.filter (Edge arcs.toFinset u)) ∧
      out.2 ≤ 1+candidates.length*(2*arcs.length+10) := by
  obtain ⟨same, work⟩ := leastWhereWithChecks_spec
    (fun v => memScanWithWordWork (u,v) arcs) (Edge arcs.toFinset u) candidates (2*arcs.length+1)
    (fun v _ => (memScanWithWordWork_spec (u,v) arcs).1.trans (Bool.eq_iff_iff.mpr (by simp [Edge])))
    (fun v _ => (memScanWithWordWork_spec (u,v) arcs).2)
  exact ⟨same,(Nat.add_le_add_right (Nat.add_le_add_right work _) _).trans_eq (by ring)⟩

omit [Fintype V] in
private def nextVertexWithWordWork (G H : List (V × V)) (R : List V) (u : V) : Option V × ℕ :=
  let old := leastSuccessorWithWordWork H u R
  let new := leastSuccessorWithWordWork G u R
  (old.1.or new.1,old.2+new.2+6)

omit [Fintype V] in
private theorem nextVertexWithWordWork_spec (G H : List (V × V)) (R : List V) (u : V) :
    let out := nextVertexWithWordWork G H R u
    out.1 = nextVertex G.toFinset H.toFinset R.toFinset u ∧
      out.2 ≤ 8+R.length*(2*(G.length+H.length)+20) := by
  obtain ⟨old, oldWork⟩ := leastSuccessorWithWordWork_spec H u R
  obtain ⟨new, newWork⟩ := leastSuccessorWithWordWork_spec G u R
  simp only [nextVertexWithWordWork,old,new,nextVertex,true_and]
  exact (Nat.add_le_add_right (Nat.add_le_add oldWork newWork) 6).trans_eq (by ring)

omit [Fintype V] in
private def growListWithWordWork (G H : List (V × V)) (R : List V) (t : V) :
    ℕ → V → Option (List (V × V)) × ℕ :=
  growListWithWork (nextVertexWithWordWork G H R) 5 9 t

omit [Fintype V] in
private theorem growListWithWordWork_spec (G H : List (V × V)) (R : List V) (t : V) (k : ℕ) (u : V) :
    let out := growListWithWordWork G H R t k u
    out.1 = growFrom G.toFinset H.toFinset R.toFinset t k u ∧
      out.2 ≤ (k+1)*(17+R.length*(2*(G.length+H.length)+20)) ∧
      (out.1.getD []).length ≤ k := by
  have compiled := growListWithWork_spec G H R (nextVertexWithWordWork G H R) 5 9
    (8+R.length*(2*(G.length+H.length)+20)) t k u (by omega) (nextVertexWithWordWork_spec G H R)
  simpa only [growListWithWordWork, ← Nat.add_assoc] using compiled

/-- A source-level tally for one priority path, with the vertex-count
parameter supplied to the evaluator. Counter-only arithmetic and scans
are excluded. -/
def forwardPathListWithWordWork (G H : List (V × V)) (s t : V) (depth : ℕ) : Option (List (V × V)) × ℕ :=
  let reach := reachInListWithWordWork G t depth
  let path := growListWithWordWork G H reach.1 t depth s
  (path.1, reach.2+path.2+4)

theorem forwardPathListWithWordWork_spec (G H : List (V × V)) (s t : V) :
    let n := Fintype.card V
    let out := forwardPathListWithWordWork G H s t n
    out.1 = forwardPath G.toFinset H.toFinset s t ∧
      out.2 ≤ reachInListWordBudget n G.length+(n+1)*(17+n*(2*(G.length+H.length)+20))+4 ∧
      (out.1.getD []).length ≤ n := by
  let n := Fintype.card V
  let reach := reachInListWithWordWork G t n
  obtain ⟨simple, correct, work⟩ := reachInListWithWordWork_spec G t n
  have count : reach.1.length ≤ n := by
    rw [← List.toFinset_card_of_nodup simple]
    exact card_le_univ _
  obtain ⟨path, growing, length⟩ := growListWithWordWork_spec G H reach.1 t n s
  have same : (forwardPathListWithWordWork G H s t n).1 = forwardPath G.toFinset H.toFinset s t := by
    change (growListWithWordWork G H reach.1 t n s).1 = _
    rw [path, show reach.1.toFinset = _ from correct]
    rfl
  exact ⟨same, Nat.add_le_add_right (Nat.add_le_add work (growing.trans (by gcongr))) 4, length⟩

private def forwardStepWithWordWork (G H : List (V × V)) (depth : ℕ) (d : V × V) : List (V × V) × ℕ :=
  let chosen := forwardPathListWithWordWork G H d.1 d.2 depth
  let edges := chosen.1.getD []
  let inserted := insertListWithChecks edges H
  (inserted.1, chosen.2+2*inserted.2+12*edges.length+7)

def forwardStepWordBudget (n m : ℕ) : ℕ :=
  reachInListWordBudget n m+(n+1)*(17+n*(2*(m+n^2)+20))+4+2*(n*n^2)+12*n+7

private theorem forwardStepWithWordWork_spec (G H : List (V × V)) (d : V × V) (simple : H.Nodup) :
    let n := Fintype.card V
    let out := forwardStepWithWordWork G H n d
    out.1.Nodup ∧ out.1.toFinset = forwardStep G.toFinset H.toFinset d ∧
      out.2 ≤ forwardStepWordBudget n G.length := by
  let n := Fintype.card V
  let chosen := forwardPathListWithWordWork G H d.1 d.2 n
  let edges := chosen.1.getD []
  let inserted := insertListWithChecks edges H
  obtain ⟨path, pathWork, len⟩ := forwardPathListWithWordWork_spec G H d.1 d.2
  have oldSize : H.length ≤ n^2 := by
    rw [← List.toFinset_card_of_nodup simple, pow_two, ← Fintype.card_prod]
    exact card_le_univ _
  have changed : chosen.2 ≤ reachInListWordBudget n G.length+(n+1)*(17+n*(2*(G.length+n^2)+20))+4 :=
    pathWork.trans (by gcongr)
  obtain ⟨clean, union, costs⟩ := insertListWithChecks_spec edges H simple
  have insertBudget : inserted.2 ≤ n*n^2 := by
    apply costs.trans
    rw [Fintype.card_prod, ← pow_two]
    exact Nat.mul_le_mul_right _ len
  refine ⟨clean, ?_, ?_⟩
  · change inserted.1.toFinset = _
    rw [union, forwardStep, forwardEdges]
    change chosen.1 = _ at path
    simp only [edges, path]
  · change chosen.2+2*inserted.2+12*edges.length+7 ≤ forwardStepWordBudget n G.length
    unfold forwardStepWordBudget
    gcongr

/-- Revised structural charges for exactly the same list-backed sequence of
priority searches and insertions. The depth is supplied once by the caller. -/
def forwardRunListWithWordWork (G : List (V × V)) (depth : ℕ) :
    List (V × V) → List (V × V) → List (V × V) × ℕ
  | [], H => (H,1)
  | d :: trace, H =>
    let first := forwardStepWithWordWork G H depth d
    let rest := forwardRunListWithWordWork G depth trace first.1
    (rest.1,4+first.2+rest.2)

theorem forwardRunListWithWordWork_spec (G D H : List (V × V)) (simple : H.Nodup) :
    let n := Fintype.card V
    let out := forwardRunListWithWordWork G n D H
    out.1.Nodup ∧ out.1.toFinset = forwardRunFrom G.toFinset H.toFinset D ∧
      out.2 ≤ 1 + D.length*(4+forwardStepWordBudget n G.length) := by
  induction D generalizing H with
  | nil => simp [forwardRunListWithWordWork,forwardRunFrom,simple]
  | cons d trace ih =>
    let n := Fintype.card V
    let first := forwardStepWithWordWork G H n d
    obtain ⟨firstSimple, firstEq, firstWork⟩ := forwardStepWithWordWork_spec G H d simple
    obtain ⟨restSimple, restEq, restWork⟩ := ih first.1 firstSimple
    refine ⟨restSimple, ?_, ?_⟩
    · change (forwardRunListWithWordWork G n trace first.1).1.toFinset = _
      change first.1.toFinset = _ at firstEq
      rw [restEq, firstEq]
      rfl
    · change first.2 ≤ forwardStepWordBudget n G.length at firstWork
      change (forwardRunListWithWordWork G n trace first.1).2 ≤
        1+trace.length*(4+forwardStepWordBudget n G.length) at restWork
      change 4 + first.2 + (forwardRunListWithWordWork G n trace first.1).2 ≤
        1+(trace.length+1)*(4+forwardStepWordBudget n G.length)
      rw [Nat.succ_mul]
      omega

/-- A bounded graph reachability test with a source-level list tally. -/
def reachTestListWithWordWork (arcs : List (V × V)) (s t : V) (depth : ℕ) : Bool × ℕ :=
  let reached := reachInListWithWordWork arcs t depth
  let member := memScanWithWordWork s reached.1
  (member.1, reached.2+member.2+4)

theorem reachTestListWithWordWork_spec (arcs : List (V × V)) (s t : V) (depth : ℕ) :
    let n := Fintype.card V
    let out := reachTestListWithWordWork arcs s t depth
    out.1 = decide (s ∈ reachIn arcs.toFinset t depth) ∧
      out.2 ≤ 2 + depth*(5+arcs.length*(14+4*n))+2*n+5 := by
  let n := Fintype.card V
  let reached := reachInListWithWordWork arcs t depth
  obtain ⟨simple, same, work⟩ := reachInListWithWordWork_spec arcs t depth
  have size : reached.1.length ≤ n := by
    rw [← List.toFinset_card_of_nodup simple]
    exact card_le_univ _
  obtain ⟨member, scan⟩ := memScanWithWordWork_spec s reached.1
  have scanBound : (memScanWithWordWork s reached.1).2 ≤ 2*n+1 := scan.trans (by gcongr)
  refine ⟨?_, (Nat.add_le_add_right (Nat.add_le_add work scanBound) 4).trans_eq (by ring)⟩
  change (memScanWithWordWork s reached.1).1 = _
  rw [member, ← show reached.1.toFinset = _ from same]
  simp only [List.mem_toFinset]


end OnlineReachabilityPreservers

namespace OnlineReachabilityPreservers

variable {V : Type*} [LinearOrder V] [Fintype V]

/-- Keep the reverse-reach list used by the priority path search. -/
def forwardPathWithReachListWork (G H : List (V × V)) (s t : V) (depth : ℕ) :
    (Option (List (V × V)) × List V) × ℕ :=
  let reach := reachInListWithWordWork G t depth
  let path := growListWithWordWork G H reach.1 t depth s
  ((path.1,reach.1),reach.2+path.2+4)

theorem forwardPathWithReachListWork_spec (G H : List (V × V)) (s t : V) :
    let n := Fintype.card V
    let out := forwardPathWithReachListWork G H s t n
    (out.1.1,out.2) = forwardPathListWithWordWork G H s t n ∧
      out.1.2.length = (reaches G.toFinset t).card := by
  have reach := reachInListWithWordWork_spec G t (Fintype.card V)
  refine ⟨rfl,?_⟩
  change (reachInListWithWordWork G t (Fintype.card V)).1.length = _
  rw [← List.toFinset_card_of_nodup reach.1,reach.2.1]
  rfl

end OnlineReachabilityPreservers
