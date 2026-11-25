import OnlineReachabilityPreservers.DeterministicListWork
import OnlineReachabilityPreservers.SteinerBitBudget

/-! Stream the fixed trace through the Steiner evaluator, sharing repeats. -/

namespace OnlineReachabilityPreservers

private def extendFirstOccurrences {V : Type*} [DecidableEq V] (seen : List (V × V)) (d : V × V) :=
  if d.1 = d.2 ∨ d ∈ seen then seen else seen ++ [d]

private def nonselfRequestIsNewWithWordWork {V : Type*} [DecidableEq V] (seenRev : List (V × V))
    (d : V × V) : Bool × ℕ :=
  if d.1 = d.2 then (false,6)
  else
    let found := memScanWithWordWork d seenRev
    (!found.1,found.2+9)

private theorem nonselfRequestIsNewWithWordWork_spec {V : Type*} [DecidableEq V]
    (seenRev : List (V × V)) (d : V × V) :
    let out := nonselfRequestIsNewWithWordWork seenRev d
    (out.1 = true ↔ d.1 ≠ d.2 ∧ d ∉ seenRev) ∧ out.2 ≤ 2*seenRev.length+10 := by
  unfold nonselfRequestIsNewWithWordWork
  by_cases self : d.1 = d.2
  · simp [self]
  · obtain ⟨result,work⟩ := memScanWithWordWork_spec d seenRev
    rw [ite_eq_right self]
    refine ⟨by simp [result,self],?_⟩
    change (memScanWithWordWork d seenRev).2+9 ≤ _
    omega

private def replayFirstOccurrencesFrom {V X : Type*} [DecidableEq V] (evaluate : List (V × V) → X × ℕ)
    (reverseSeen : List (V × V)) (previous : X) : List (V × V) → List X × ℕ × ℕ
  | [] => ([previous],3,0)
  | d :: tail =>
    let next := nonselfRequestIsNewWithWordWork reverseSeen d
    if next.1 then
      let seen := d :: reverseSeen
      let value := evaluate seen.reverse
      let replay := replayFirstOccurrencesFrom evaluate seen value.1 tail
      (previous :: replay.1, replay.2.1+next.2+8*(reverseSeen.length+1)+21+value.2,replay.2.2+1)
    else
      let replay := replayFirstOccurrencesFrom evaluate reverseSeen previous tail
      (previous :: replay.1, replay.2.1+next.2+13,replay.2.2)

private theorem replayFirstOccurrencesFrom_spec {V X : Type*} [DecidableEq V]
    (evaluate : List (V × V) → X × ℕ) (B C : ℕ)
    (valid : V × V → Prop)
    (evalWork : ∀ P, P.length ≤ B → (∀ d ∈ P, valid d) → (evaluate P).2 ≤ C)
    (seen pending : List (V × V)) (fits : seen.length+pending.length ≤ B)
    (seenValid : ∀ d ∈ seen, valid d) (pendingValid : ∀ d ∈ pending, valid d) :
    let out := replayFirstOccurrencesFrom evaluate seen (evaluate seen.reverse).1 pending
    out.1 = pending.inits.map (fun P => (evaluate (P.foldl extendFirstOccurrences seen.reverse)).1) ∧
      out.2.1 ≤ pending.length*(10*B+31+C)+3 ∧
      seen.length+out.2.2 = (pending.foldl extendFirstOccurrences seen.reverse).length := by
  induction pending generalizing seen with
  | nil => simp [replayFirstOccurrencesFrom]
  | cons d tail ih =>
    obtain ⟨accept,charge⟩ := nonselfRequestIsNewWithWordWork_spec seen d
    have room : seen.length+tail.length+1 ≤ B := by simpa only [List.length_cons, Nat.add_assoc] using fits
    have tailValid : ∀ r ∈ tail, valid r := fun r h => pendingValid r (List.mem_cons_of_mem _ h)
    by_cases new : (nonselfRequestIsNewWithWordWork seen d).1 = true
    · have allowed := accept.mp new
      have absent : d ∉ seen.reverse := by simpa using allowed.2
      have extend : extendFirstOccurrences seen.reverse d = (d::seen).reverse := by
        simp [extendFirstOccurrences,allowed.1,absent]
      have enlarged : ∀ r ∈ d::seen, valid r := by
        intro r h
        rcases List.mem_cons.mp h with equal | prior
        · exact equal.symm ▸ pendingValid d List.mem_cons_self
        · exact seenValid r prior
      obtain ⟨prefixes,work,calls⟩ := ih (d::seen) (by simp only [List.length_cons]; omega) enlarged tailValid
      have costs := evalWork ((d::seen).reverse) (by simp only [List.length_reverse,List.length_cons]; omega)
        (fun r h => enlarged r (List.mem_reverse.mp h))
      rw [replayFirstOccurrencesFrom, ite_eq_left new]
      dsimp only
      refine ⟨?_, ?_, ?_⟩
      · rw [List.inits_cons, List.map_cons, List.foldl_nil, List.map_map, prefixes]
        apply congrArg (List.cons (evaluate seen.reverse).1)
        apply List.map_congr_left
        intro P _
        change (evaluate (P.foldl extendFirstOccurrences (d::seen).reverse)).1 =
          (evaluate ((d::P).foldl extendFirstOccurrences seen.reverse)).1
        rw [List.foldl_cons, extend]
      · rw [List.length_cons, Nat.succ_mul tail.length (10*B+31+C)]
        omega
      · rw [List.foldl_cons, extend]
        simp only [List.length_cons] at calls
        omega
    · have unchanged : extendFirstOccurrences seen.reverse d = seen.reverse := by
        by_cases self : d.1 = d.2
        · simp [extendFirstOccurrences,self]
        by_cases visited : d ∈ seen.reverse
        · simp [extendFirstOccurrences,visited]
        exact (new (accept.mpr ⟨self,by simpa using visited⟩)).elim
      obtain ⟨prefixes,work,calls⟩ := ih seen (by omega) seenValid tailValid
      rw [replayFirstOccurrencesFrom, ite_eq_right new]
      dsimp only
      refine ⟨?_, ?_, ?_⟩
      · rw [List.inits_cons, List.map_cons, List.foldl_nil, List.map_map, prefixes]
        apply congrArg (List.cons (evaluate seen.reverse).1)
        apply List.map_congr_left
        intro P _
        change (evaluate (P.foldl extendFirstOccurrences seen.reverse)).1 =
          (evaluate ((d::P).foldl extendFirstOccurrences seen.reverse)).1
        rw [List.foldl_cons, unchanged]
      · rw [List.length_cons, Nat.succ_mul tail.length (10*B+31+C)]
        omega
      · rw [List.foldl_cons, unchanged]
        exact calls

/-- Reuse the preceding result for a self demand or a repeated demand.
The second field counts trace maintenance and the measured callback work.
The third field records the number of evaluations. -/
def replayFirstOccurrencesWithWordWork {V X : Type*} [DecidableEq V]
    (evaluate : List (V × V) → X × ℕ) (D : List (V × V)) : List X × ℕ × ℕ :=
  let first := evaluate []
  let out := replayFirstOccurrencesFrom evaluate [] first.1 D
  (out.1,out.2.1+first.2+4,out.2.2+1)

/-- The callback needs its bound only on demands satisfying the trace invariant. -/
theorem replayFirstOccurrencesWithWordWork_spec_of_demand_property {V X : Type*} [LinearOrder V]
    (evaluate : List (V × V) → X × ℕ) (D : List (V × V)) (C : ℕ)
    (valid : V × V → Prop)
    (evalWork : ∀ P, P.length ≤ D.length → (∀ d ∈ P, valid d) → (evaluate P).2 ≤ C)
    (fullValid : ∀ d ∈ D, valid d) :
    let out := replayFirstOccurrencesWithWordWork evaluate D
    out.1 = D.inits.map (fun P => (evaluate (distinctNonselfTrace P)).1) ∧
      out.2.1 ≤ D.length*(10*D.length+31+C)+C+7 ∧ out.2.2 = (distinctNonselfTrace D).length+1 := by
  obtain ⟨prefixes,work,calls⟩ := replayFirstOccurrencesFrom_spec evaluate D.length C valid evalWork [] D
    (by simp) (by simp) fullValid
  have same (P : List (V × V)) : P.foldl extendFirstOccurrences [] = distinctNonselfTrace P := rfl
  simp only [List.reverse_nil,same,List.length_nil, Nat.zero_add] at prefixes work calls
  refine ⟨prefixes,?_,congrArg (· + 1) calls⟩
  have first := evalWork [] (by simp) (by simp)
  dsimp only [replayFirstOccurrencesWithWordWork]
  omega

theorem replayFirstOccurrencesWithWordWork_spec {V X : Type*} [LinearOrder V]
    (evaluate : List (V × V) → X × ℕ) (D : List (V × V)) (C : ℕ)
    (evalWork : ∀ P, P.length ≤ D.length → (evaluate P).2 ≤ C) :
    let out := replayFirstOccurrencesWithWordWork evaluate D
    out.1 = D.inits.map (fun P => (evaluate (distinctNonselfTrace P)).1) ∧
      out.2.1 ≤ D.length*(10*D.length+31+C)+C+7 ∧ out.2.2 = (distinctNonselfTrace D).length+1 :=
  replayFirstOccurrencesWithWordWork_spec_of_demand_property evaluate D C (fun _ => True)
    (fun P len _ => evalWork P len) (by simp)

private theorem replayFirstOccurrencesFrom_records_eq {V X : Type*} [DecidableEq V]
    (first second : List (V × V) → X × ℕ) (same : ∀ P, (first P).1 = (second P).1)
    (seen : List (V × V)) (previous : X) (D : List (V × V)) :
    let left := replayFirstOccurrencesFrom first seen previous D
    let right := replayFirstOccurrencesFrom second seen previous D
    left.1 = right.1 ∧ left.2.2 = right.2.2 := by
  induction D generalizing seen previous with
  | nil => exact ⟨rfl,rfl⟩
  | cons d rest ih =>
    by_cases accepted : (nonselfRequestIsNewWithWordWork seen d).1 = true
    · obtain ⟨records,calls⟩ := ih (d::seen) (second (d::seen).reverse).1
      simp only [replayFirstOccurrencesFrom,accepted,ite_true,same,records,calls,and_self]
    · obtain ⟨records,calls⟩ := ih seen previous
      simp only [replayFirstOccurrencesFrom,accepted,Bool.false_eq_true,ite_false,records,calls,and_self]

/-- The records and evaluation count depend only on the callback values. -/
theorem replayFirstOccurrencesWithWordWork_records_eq {V X : Type*} [DecidableEq V]
    (first second : List (V × V) → X × ℕ) (same : ∀ P, (first P).1 = (second P).1)
    (D : List (V × V)) :
    let left := replayFirstOccurrencesWithWordWork first D
    let right := replayFirstOccurrencesWithWordWork second D
    left.1 = right.1 ∧ left.2.2 = right.2.2 := by
  obtain ⟨records,calls⟩ := replayFirstOccurrencesFrom_records_eq first second same [] (second []).1 D
  simp only [replayFirstOccurrencesWithWordWork,same,records,calls,and_self]

section SteinerTrace

variable {V : Type*} [LinearOrder V] [Fintype V]

omit [Fintype V] in
private def steinerFallbackPrefixFromWithWordWork (G : Arcs V) (seen : Bool) :
    List (V × V) → List (Arcs V × ℕ) × ℕ
  | [] => ([(if seen then G else ∅,0)],6)
  | d :: D =>
    let rest := steinerFallbackPrefixFromWithWordWork G (seen || decide (d.1 ≠ d.2)) D
    ((if seen then G else ∅,0) :: rest.1,rest.2+16)

omit [Fintype V] in
private theorem steinerFallbackPrefixFromWithWordWork_spec (G : Arcs V) (seen : Bool) (D : List (V × V)) :
    let out := steinerFallbackPrefixFromWithWordWork G seen D
    out.1 = (D.scanl (fun prev d => prev || decide (d.1 ≠ d.2)) seen).map
      (fun havingDemand => (if havingDemand then G else ∅,0)) ∧
      out.2 = 16*D.length+6 := by
  induction D generalizing seen with
  | nil => simp [steinerFallbackPrefixFromWithWordWork]
  | cons d D ih =>
    obtain ⟨same,work⟩ := ih (seen || decide (d.1 ≠ d.2))
    rw [steinerFallbackPrefixFromWithWordWork]
    dsimp only
    constructor
    · rw [same,List.scanl_cons,List.map_cons]
    · rw [work,List.length_cons,Nat.mul_succ 16 D.length]

/-- Count the exact exhausted-word pass along with its prefix graphs. -/
def steinerFallbackPrefixScanWithWordWork (G : Arcs V) (D : List (V × V)) :=
  steinerFallbackPrefixFromWithWordWork G false D

omit [Fintype V] in
theorem steinerFallbackPrefixScanWithWordWork_spec (G : Arcs V) (D : List (V × V)) :
    let out := steinerFallbackPrefixScanWithWordWork G D
    out.1 = steinerFallbackPrefixScan G D ∧ out.2 = 16*D.length+6 :=
  steinerFallbackPrefixFromWithWordWork_spec G false D

end SteinerTrace

end OnlineReachabilityPreservers
