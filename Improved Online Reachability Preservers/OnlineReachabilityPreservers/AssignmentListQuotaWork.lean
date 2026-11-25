import OnlineReachabilityPreservers.DeterministicListWork
import OnlineReachabilityPreservers.KnownBudget

/-! List-backed evaluation of the known-quota path rule and finite budget certification. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V : Type*} [LinearOrder V] [Fintype V]

private def quotaTrialWordBudget (n m : ℕ) : ℕ :=
  1+(4+forwardStepWordBudget n m)+6*n^2+12

/-- Test a candidate by executing its purchase on a temporary list.
The increase in the number of edges is the new-edge count. -/
def quotaTrialWithWordWork (G H : List (V × V)) (depth p F : ℕ) (d : V × V) : Bool × ℕ :=
  let purchased := forwardRunListWithWordWork G depth [d] H
  (decide (F < p*(purchased.1.length-H.length)), purchased.2+3*(purchased.1.length+H.length)+12)

theorem quotaTrialWithWordWork_spec (G H : List (V × V)) (p F : ℕ) (d : V × V) (simple : H.Nodup) :
    let n := Fintype.card V
    let out := quotaTrialWithWordWork G H n p F d
    out.1 = decide (F < p*(pathArcs (forwardPath G.toFinset H.toFinset d.1 d.2) \ H.toFinset).card) ∧
      out.2 ≤ quotaTrialWordBudget n G.length := by
  let n := Fintype.card V
  let purchased := forwardRunListWithWordWork G n [d] H
  obtain ⟨purchasedSimple, same, tally⟩ := forwardRunListWithWordWork_spec G [d] H simple
  have size (K : List (V × V)) (nodup : K.Nodup) : K.length ≤ n^2 := by
    rw [← List.toFinset_card_of_nodup nodup, pow_two, ← Fintype.card_prod]
    exact card_le_univ _
  have delta : purchased.1.length-H.length =
      (pathArcs (forwardPath G.toFinset H.toFinset d.1 d.2) \ H.toFinset).card := by
    change purchased.1.toFinset = forwardStep G.toFinset H.toFinset d at same
    rw [← List.toFinset_card_of_nodup purchasedSimple, ← List.toFinset_card_of_nodup simple, same, forwardStep,
      union_comm, ← card_sdiff_add_card]
    simp [forwardEdges, pathArcs]
  refine ⟨?_,?_⟩
  · change decide (F < p*(purchased.1.length-H.length)) = _
    rw [delta]
  · change purchased.2+3*(purchased.1.length+H.length)+12 ≤ _
    have each : purchased.2 ≤ 1+(4+forwardStepWordBudget n G.length) := by
      simpa only [List.length_singleton, one_mul] using tally
    have cap := Nat.mul_le_mul_left 3 (Nat.add_le_add (size purchased.1 purchasedSimple) (size H simple))
    exact (Nat.add_le_add_right (Nat.add_le_add each cap) 12).trans_eq (by unfold quotaTrialWordBudget; ring)

private def expensiveDemandWordBudget (n m q : ℕ) : ℕ :=
  q*(quotaTrialWordBudget n m+19)+8

/-- Test all candidate demands and return the lexicographically first one
whose purchase exceeds the per-request budget. -/
def expensiveDemandWithWordWork (G H : List (V × V)) (depth p F : ℕ)
    (Q : List (V × V)) : Option (V × V) × ℕ :=
  let keys := Q.map toLex
  let chosen := leastWhereWithChecks (fun key => quotaTrialWithWordWork G H depth p F (ofLex key)) keys
  (chosen.1.map ofLex, chosen.2+18*Q.length+8)

theorem expensiveDemandWithWordWork_spec (G H Q : List (V × V)) (p F : ℕ) (simple : H.Nodup) :
    let n := Fintype.card V
    let out := expensiveDemandWithWordWork G H n p F Q
    out.1 = (least? ((Q.toFinset.filter
      (fun d => F < p*(pathArcs (forwardPath G.toFinset H.toFinset d.1 d.2) \ H.toFinset).card)).image toLex)).map ofLex ∧
      out.2 ≤ expensiveDemandWordBudget n G.length Q.length := by
  let n := Fintype.card V
  let test := fun key : Lex (V × V) => quotaTrialWithWordWork G H n p F (ofLex key)
  let predicate := fun d : V × V => F < p*(pathArcs (forwardPath G.toFinset H.toFinset d.1 d.2) \ H.toFinset).card
  let keys := Q.map toLex
  obtain ⟨tested, charge⟩ := leastWhereWithChecks_spec test (fun key => predicate (ofLex key)) keys
    (quotaTrialWordBudget n G.length)
    (fun key _ => (quotaTrialWithWordWork_spec G H p F (ofLex key) simple).1)
    (fun key _ => (quotaTrialWithWordWork_spec G H p F (ofLex key) simple).2)
  have filterEq : keys.toFinset.filter (fun key => predicate (ofLex key)) = (Q.toFinset.filter predicate).image toLex := by
    ext a
    simp only [keys, mem_filter, mem_image, List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨⟨d, on, rfl⟩, exceeds⟩
      exact ⟨d, ⟨on, exceeds⟩, rfl⟩
    · rintro ⟨d, ⟨on, exceeds⟩, rfl⟩
      exact ⟨⟨d,on,rfl⟩, exceeds⟩
  constructor
  · change (leastWhereWithChecks test keys).1.map ofLex = _
    rw [tested, filterEq]
  · change (leastWhereWithChecks test keys).2+18*Q.length+8 ≤ _
    have qLen : keys.length = Q.length := List.length_map _
    rw [qLen] at charge
    exact (Nat.add_le_add_right (Nat.add_le_add_right charge _) _).trans_eq (by unfold expensiveDemandWordBudget; ring)

private def forwardQuotaRule (G : List (V × V)) : PathRule V :=
  fun A d => forwardPath G.toFinset A d.1 d.2

private def quotaPurchaseWordBudget (n m : ℕ) : ℕ := 1+(4+forwardStepWordBudget n m)

private def quotaTraceStepWordBudget (n m q : ℕ) : ℕ :=
  expensiveDemandWordBudget n m q + quotaPurchaseWordBudget n m + 8*q+12

private theorem quotaTraceStepWordBudget_mono (n m : ℕ) : Monotone (quotaTraceStepWordBudget n m) := by
  intro a b ab
  unfold quotaTraceStepWordBudget expensiveDemandWordBudget
  gcongr

private def quotaTraceWithWordWork (G : List (V × V)) (depth p F : ℕ) :
    ℕ → List (V × V) → List (V × V) → (List (V × V) × List (V × V)) × ℕ
  | 0, H, _ => (([],H),1)
  | k+1, H, Q =>
    let chosen := expensiveDemandWithWordWork G H depth p F Q
    match chosen.1 with
    | none => (([],H),chosen.2+6)
    | some d =>
      let next := forwardRunListWithWordWork G depth [d] H
      let remaining := Q.filter (fun e => decide (d ≠ e))
      let tail := quotaTraceWithWordWork G depth p F k next.1 remaining
      ((d::tail.1.1,tail.1.2),chosen.2+next.2+8*Q.length+12+tail.2)

private theorem quotaTraceWithWordWork_spec (G H Q : List (V × V)) (p F k : ℕ) (simple : H.Nodup) :
    let n := Fintype.card V
    let rule := forwardQuotaRule G
    let out := quotaTraceWithWordWork G n p F k H Q
    out.1.1 = expensiveTrace rule p F k H.toFinset Q.toFinset ∧
      out.1.2.Nodup ∧ out.1.2.toFinset = runRule rule H.toFinset out.1.1 ∧
      out.1.1.length ≤ k ∧ out.2 ≤ 1+k*quotaTraceStepWordBudget n G.length Q.length := by
  dsimp only
  induction k generalizing H Q with
  | zero => simp [quotaTraceWithWordWork, expensiveTrace.eq_1, runRule, simple]
  | succ k ih =>
    let n := Fintype.card V
    let rule := forwardQuotaRule G
    let chosen := expensiveDemandWithWordWork G H n p F Q
    obtain ⟨who, firstWork⟩ := expensiveDemandWithWordWork_spec G H Q p F simple
    have agreement : chosen.1 = expensive rule p F H.toFinset Q.toFinset := who
    change chosen.2 ≤ expensiveDemandWordBudget n G.length Q.length at firstWork
    cases found : chosen.1 with
    | none =>
      have empty : expensive rule p F H.toFinset Q.toFinset = none := agreement.symm.trans found
      have direct : quotaTraceWithWordWork G n p F (k+1) H Q = (([],H),chosen.2+6) := by
        rw [quotaTraceWithWordWork, show (expensiveDemandWithWordWork G H n p F Q).1 = none from found]
      have checked : expensiveTrace rule p F (k+1) H.toFinset Q.toFinset = [] := by
        rw [expensiveTrace.eq_2, empty]
      rw [direct, checked]
      refine ⟨rfl, simple, rfl, Nat.zero_le _, ?_⟩
      have cap : chosen.2+6 ≤ quotaTraceStepWordBudget n G.length Q.length := by
        unfold quotaTraceStepWordBudget
        omega
      exact cap.trans <| (Nat.le_mul_of_pos_left _ (Nat.succ_pos k)).trans (Nat.le_add_left _ _)
    | some d =>
      have selected : expensive rule p F H.toFinset Q.toFinset = some d := agreement.symm.trans found
      let next := forwardRunListWithWordWork G n [d] H
      let remaining := Q.filter (fun e => decide (d ≠ e))
      let tail := quotaTraceWithWordWork G n p F k next.1 remaining
      obtain ⟨nextSimple, purchase, paid⟩ := forwardRunListWithWordWork_spec G [d] H simple
      have nextSet : next.1.toFinset = H.toFinset ∪ pathArcs (rule H.toFinset d) := purchase
      have paidBound : next.2 ≤ quotaPurchaseWordBudget n G.length := by
        simpa only [quotaPurchaseWordBudget, List.length_singleton, one_mul] using paid
      have erase : remaining.toFinset = Q.toFinset.erase d := by
        ext v
        simp only [remaining, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, mem_erase]
        exact ⟨fun ⟨on,different⟩ => ⟨Ne.symm different,on⟩, fun ⟨different,on⟩ => ⟨on,Ne.symm different⟩⟩
      obtain ⟨trace, tailSimple, state, length, work⟩ := ih next.1 remaining nextSimple
      have expected : expensiveTrace rule p F (k+1) H.toFinset Q.toFinset =
          d :: expensiveTrace rule p F k next.1.toFinset remaining.toFinset := by
        rw [expensiveTrace.eq_2, selected]
        change d :: expensiveTrace rule p F k (H.toFinset ∪ pathArcs (rule H.toFinset d)) (Q.toFinset.erase d) = _
        rw [← nextSet, ← erase]
      have result : quotaTraceWithWordWork G n p F (k+1) H Q =
          ((d::tail.1.1,tail.1.2),chosen.2+next.2+8*Q.length+12+tail.2) := by
        rw [quotaTraceWithWordWork, show (expensiveDemandWithWordWork G H n p F Q).1 = some d from found]
      rw [result, expected]
      refine ⟨congrArg (d::·) trace, tailSimple, ?_, Nat.succ_le_succ length, ?_⟩
      · change tail.1.2.toFinset = runRule rule H.toFinset (d::tail.1.1)
        rw [state, nextSet]
        rfl
      · change chosen.2+next.2+8*Q.length+12+tail.2 ≤ 1+(k+1)*quotaTraceStepWordBudget n G.length Q.length
        have remainingSize : remaining.length ≤ Q.length := List.length_filter_le _ _
        have tailBound : tail.2 ≤ 1+k*quotaTraceStepWordBudget n G.length Q.length :=
          work.trans (Nat.add_le_add_left (Nat.mul_le_mul_left k (quotaTraceStepWordBudget_mono n G.length remainingSize)) 1)
        have firstBound : chosen.2+next.2+8*Q.length+12 ≤ quotaTraceStepWordBudget n G.length Q.length := by
          exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add firstWork paidBound) _) _
        exact (Nat.add_le_add firstBound tailBound).trans_eq (by
          rw [Nat.succ_mul k (quotaTraceStepWordBudget n G.length Q.length)]
          ac_rfl)

private def quotaCertificateTrialWithWordWork (G Q : List (V × V)) (depth p F : ℕ) : Bool × ℕ :=
  let planned := quotaTraceWithWordWork G depth p F p [] Q
  let steps := planned.1.1.length
  let bought := planned.1.2.length
  (decide (steps < p ∧ bought ≤ F),planned.2+3*(steps+bought)+12)

private def quotaCertificateTrialWordBudget (n m q p : ℕ) : ℕ :=
  1+p*quotaTraceStepWordBudget n m q+3*(p+n^2)+12

private theorem quotaCertificateTrialWithWordWork_spec (G Q : List (V × V)) (p F : ℕ) :
    let n := Fintype.card V
    let out := quotaCertificateTrialWithWordWork G Q n p F
    out.1 = decide (KnownBudgetCertified (forwardQuotaRule G) Q.toFinset p F) ∧
      out.2 ≤ quotaCertificateTrialWordBudget n G.length Q.length p := by
  let n := Fintype.card V
  let planned := quotaTraceWithWordWork G n p F p [] Q
  obtain ⟨trace, simple, state, steps, work⟩ := quotaTraceWithWordWork_spec G [] Q p F p List.nodup_nil
  have bought : planned.1.2.length ≤ n^2 := by
    rw [← List.toFinset_card_of_nodup simple, pow_two, ← Fintype.card_prod]
    exact card_le_univ _
  refine ⟨?_,?_⟩
  · apply Bool.eq_iff_iff.mpr
    change decide (planned.1.1.length < p ∧ planned.1.2.length ≤ F) = true ↔
      decide (KnownBudgetCertified (forwardQuotaRule G) Q.toFinset p F) = true
    simp only [decide_eq_true_eq]
    unfold KnownBudgetCertified
    change (planned.1.1.length < p ∧ planned.1.2.length ≤ F) ↔
      (expensiveTrace (forwardQuotaRule G) p F p ∅ Q.toFinset).length < p ∧
        (runRule (forwardQuotaRule G) ∅ (expensiveTrace (forwardQuotaRule G) p F p ∅ Q.toFinset)).card ≤ F
    rw [← List.toFinset_card_of_nodup simple]
    change planned.1.2.toFinset = runRule (forwardQuotaRule G) ∅ planned.1.1 at state
    change planned.1.1 = expensiveTrace (forwardQuotaRule G) p F p ∅ Q.toFinset at trace
    rw [state, trace]
  · change planned.2+3*(planned.1.1.length+planned.1.2.length)+12 ≤ _
    exact Nat.add_le_add_right (Nat.add_le_add work (Nat.mul_le_mul_left 3 (Nat.add_le_add steps bought))) 12

/-- Certify the smallest budget with an explicit tally for the preparation,
candidate scans, and temporary purchases in all tested budgets. -/
def certifiedBudgetListWithWordWork (G Q : List (V × V)) (depth p cap : ℕ) : ℕ × ℕ :=
  let chosen := leastWhereWithChecks (quotaCertificateTrialWithWordWork G Q depth p) (List.range (cap+1))
  (chosen.1.getD cap,chosen.2+14*(cap+1)+5)

theorem certifiedBudgetListWithWordWork_spec (G Q : List (V × V)) (p cap : ℕ) :
    let n := Fintype.card V
    let out := certifiedBudgetListWithWordWork G Q n p cap
    out.1 = certifiedBudget (forwardQuotaRule G) Q.toFinset p cap ∧
      out.2 ≤ (cap+1)*(quotaCertificateTrialWordBudget n G.length Q.length p+15)+5 := by
  let n := Fintype.card V
  let test := quotaCertificateTrialWithWordWork G Q n p
  let prop := KnownBudgetCertified (forwardQuotaRule G) Q.toFinset p
  obtain ⟨same, count⟩ := leastWhereWithChecks_spec test prop (List.range (cap+1))
    (quotaCertificateTrialWordBudget n G.length Q.length p)
    (fun F _ => (quotaCertificateTrialWithWordWork_spec G Q p F).1)
    (fun F _ => (quotaCertificateTrialWithWordWork_spec G Q p F).2)
  have enumeration : (List.range (cap+1)).toFinset = range (cap+1) := by ext b; simp
  constructor
  · change (leastWhereWithChecks test (List.range (cap+1))).1.getD cap = _
    rw [same, enumeration]
    rfl
  · change (leastWhereWithChecks test (List.range (cap+1))).2+14*(cap+1)+5 ≤ _
    rw [List.length_range] at count
    exact (Nat.add_le_add_right (Nat.add_le_add_right count _) _).trans_eq (by ring)

private def quotaSelectionWordBudget (n m : ℕ) : ℕ :=
  reachInListWordBudget n m+(n+1)*(17+n*(2*(m+n^2)+20))+4

private theorem quotaChoice_original (G H : List (V × V)) (d : V × V) (simple : H.Nodup) :
    let n := Fintype.card V
    let out := forwardPathListWithWordWork G H d.1 d.2 n
    out.1 = (forwardQuotaRule G) H.toFinset d ∧ out.2 ≤ quotaSelectionWordBudget n G.length := by
  obtain ⟨same, cost, _⟩ := forwardPathListWithWordWork_spec G H d.1 d.2
  have small : H.length ≤ Fintype.card V^2 := by
    rw [← List.toFinset_card_of_nodup simple, pow_two, ← Fintype.card_prod]
    exact card_le_univ _
  refine ⟨same,cost.trans ?_⟩
  unfold quotaSelectionWordBudget
  gcongr

private def replayAssignmentWithWordWork (G : List (V × V)) (depth : ℕ) (d : V × V) :
    List (V × V) → List (V × V) → Option (List (V × V)) × ℕ
  | [], H =>
    let result := forwardPathListWithWordWork G H d.1 d.2 depth
    (result.1,result.2+5)
  | a::tail, H =>
    if a = d then
      let result := forwardPathListWithWordWork G H d.1 d.2 depth
      (result.1,result.2+5)
    else
      let purchased := forwardRunListWithWordWork G depth [a] H
      let result := replayAssignmentWithWordWork G depth d tail purchased.1
      (result.1,purchased.2+result.2+8)

private def quotaReplayStepWordBudget (n m : ℕ) : ℕ :=
  quotaSelectionWordBudget n m+quotaPurchaseWordBudget n m+8

private theorem replayAssignmentWithWordWork_spec (G H T : List (V × V)) (d : V × V) (simple : H.Nodup) :
    let n := Fintype.card V
    let out := replayAssignmentWithWordWork G n d T H
    out.1 = assignedPath (forwardQuotaRule G) H.toFinset T d ∧
      out.2 ≤ (T.length+1)*quotaReplayStepWordBudget n G.length := by
  dsimp only
  let n := Fintype.card V
  induction T generalizing H with
  | nil =>
    obtain ⟨same, cost⟩ := quotaChoice_original G H d simple
    simp only [replayAssignmentWithWordWork, assignedPath.eq_1, same, List.length_nil, zero_add, one_mul, true_and]
    have cap : (forwardPathListWithWordWork G H d.1 d.2 n).2 ≤ quotaSelectionWordBudget n G.length := cost
    change (forwardPathListWithWordWork G H d.1 d.2 n).2 + 5 ≤ quotaReplayStepWordBudget n G.length
    unfold quotaReplayStepWordBudget
    omega
  | cons a T ih =>
    by_cases matched : a = d
    · obtain ⟨same, cost⟩ := quotaChoice_original G H d simple
      subst a
      simp only [replayAssignmentWithWordWork, assignedPath.eq_2, ite_true, same, List.length_cons, true_and]
      have base : (forwardPathListWithWordWork G H d.1 d.2 n).2 + 5 ≤ quotaReplayStepWordBudget n G.length := by
        have cap : (forwardPathListWithWordWork G H d.1 d.2 n).2 ≤ quotaSelectionWordBudget n G.length := cost
        unfold quotaReplayStepWordBudget
        omega
      exact base.trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos (T.length+1)))
    · let bought := forwardRunListWithWordWork G n [a] H
      obtain ⟨nodup, edges, work⟩ := forwardRunListWithWordWork_spec G [a] H simple
      obtain ⟨same, cost⟩ := ih bought.1 nodup
      have agree : bought.1.toFinset = H.toFinset ∪ pathArcs (forwardQuotaRule G H.toFinset a) := edges
      have cap : bought.2 ≤ quotaPurchaseWordBudget n G.length := by
        simpa only [quotaPurchaseWordBudget, List.length_singleton, one_mul] using work
      simp only [replayAssignmentWithWordWork, assignedPath.eq_2, matched, ↓reduceIte, List.length_cons]
      change (replayAssignmentWithWordWork G n d T bought.1).1 =
        assignedPath (forwardQuotaRule G) (H.toFinset ∪ pathArcs (forwardQuotaRule G H.toFinset a)) T d ∧
        bought.2+(replayAssignmentWithWordWork G n d T bought.1).2+8 ≤ (T.length+1+1)*quotaReplayStepWordBudget n G.length
      refine ⟨same.trans (by rw [agree]),?_⟩
      have nextCost : (replayAssignmentWithWordWork G n d T bought.1).2 ≤ (T.length+1)*quotaReplayStepWordBudget n G.length :=
        cost
      rw [Nat.succ_mul (T.length+1)]
      have purchaseBudget : quotaPurchaseWordBudget n G.length+8 ≤ quotaReplayStepWordBudget n G.length := by
        unfold quotaReplayStepWordBudget
        omega
      omega

/-- The known-quota selector with an explicit tally for both its
preparation and the replay used to recover one assigned path. -/
def knownBudgetPathWithWordWork (G Q : List (V × V)) (depth p F : ℕ) (d : V × V) :
    Option (List (V × V)) × ℕ :=
  let planned := quotaTraceWithWordWork G depth p F p [] Q
  let selected := replayAssignmentWithWordWork G depth d planned.1.1 []
  (selected.1,planned.2+selected.2+6)

theorem knownBudgetPathWithWordWork_spec (G Q : List (V × V)) (p F : ℕ) (d : V × V) :
    let n := Fintype.card V
    let out := knownBudgetPathWithWordWork G Q n p F d
    out.1 = knownBudgetPath (forwardQuotaRule G) Q.toFinset p F d ∧
      out.2 ≤ 1+p*quotaTraceStepWordBudget n G.length Q.length+(p+1)*quotaReplayStepWordBudget n G.length+6 := by
  let n := Fintype.card V
  let plan := quotaTraceWithWordWork G n p F p [] Q
  obtain ⟨trace, _, _, len, charge⟩ := quotaTraceWithWordWork_spec G [] Q p F p List.nodup_nil
  obtain ⟨same, work⟩ := replayAssignmentWithWordWork_spec G [] plan.1.1 d List.nodup_nil
  constructor
  · change (replayAssignmentWithWordWork G n d plan.1.1 []).1 = _
    unfold knownBudgetPath
    rw [same, trace]
    rfl
  · change plan.2 + (replayAssignmentWithWordWork G n d plan.1.1 []).2 + 6 ≤ _
    exact Nat.add_le_add_right (Nat.add_le_add charge (work.trans (Nat.mul_le_mul_right _ (Nat.succ_le_succ len)))) 6

/-- Combine the certified least budget with the exact known-quota selector. -/
def certifiedQuotaPathWithWordWork (G Q : List (V × V)) (depth p cap : ℕ) (d : V × V) :
    Option (List (V × V)) × ℕ :=
  let checked := certifiedBudgetListWithWordWork G Q depth p cap
  let selected := knownBudgetPathWithWordWork G Q depth p checked.1 d
  (selected.1,checked.2+selected.2+4)

theorem certifiedQuotaPathWithWordWork_spec (G Q : List (V × V)) (p cap : ℕ) (d : V × V) :
    let n := Fintype.card V
    let m := G.length
    let q := Q.length
    let rule := forwardQuotaRule G
    let out := certifiedQuotaPathWithWordWork G Q n p cap d
    out.1 = knownBudgetPath rule Q.toFinset p (certifiedBudget rule Q.toFinset p cap) d ∧
      out.2 ≤ (cap+1)*(quotaCertificateTrialWordBudget n m q p+15)+5 +
        (1+p*quotaTraceStepWordBudget n m q+(p+1)*quotaReplayStepWordBudget n m+6)+4 := by
  let n := Fintype.card V
  let checked := certifiedBudgetListWithWordWork G Q n p cap
  let selected := knownBudgetPathWithWordWork G Q n p checked.1 d
  obtain ⟨certificate, work⟩ := certifiedBudgetListWithWordWork_spec G Q p cap
  obtain ⟨path, paid⟩ := knownBudgetPathWithWordWork_spec G Q p checked.1 d
  constructor
  · change selected.1 = _
    rw [show selected.1 = _ from path, show checked.1 = _ from certificate]
  · exact Nat.add_le_add_right (Nat.add_le_add work paid) 4

section QuotientSelection

private def pairQuotaRule (K : Arcs V) : PathRule V := fun H d => forwardPath K H d.1 d.2

private theorem pairQuotaPath_length (K : Arcs V) (p F : ℕ) (d : V × V) :
    ((knownBudgetPath (pairQuotaRule K) univ p F d).getD []).length ≤ Fintype.card V := by
  let rule := pairQuotaRule K
  let trace := expensiveTrace rule p F p ∅ univ
  obtain ⟨H,_,same⟩ := assignedPath_uses_state rule (∅ : Arcs V) trace d
  change ((assignedPath rule ∅ trace d).getD []).length ≤ _
  rw [same]
  have length := (forwardPathListWithWordWork_spec K.toList H.toList d.1 d.2).2.2
  have choice := (forwardPathListWithWordWork_spec K.toList H.toList d.1 d.2).1
  rw [choice] at length
  simpa [rule, pairQuotaRule] using length

private theorem pairQuotaPath_subset (K : Arcs V) (p F : ℕ) (d : V × V) :
    pathArcs (knownBudgetPath (pairQuotaRule K) univ p F d) ⊆ K := by
  let rule := pairQuotaRule K
  let trace := expensiveTrace rule p F p ∅ univ
  have runSubset {H : Arcs V} (T : List (V × V)) (inside : H ⊆ K) : runRule rule H T ⊆ K := by
    induction T generalizing H with
    | nil => exact inside
    | cons a T ih =>
      exact ih (union_subset inside (forwardEdges_subset inside a))
  obtain ⟨H,sub,same⟩ := assignedPath_uses_state rule (∅ : Arcs V) trace d
  change pathArcs (assignedPath rule ∅ trace d) ⊆ K
  rw [same]
  exact forwardEdges_subset (sub.trans (runSubset trace (empty_subset _))) d

/-- The quotient edge set used to lift one preassigned pair. -/
def onePairQuotaArcs (p : ℕ) (K : Arcs V) : List (V × V) → Arcs V
  | [] => ∅
  | d::_ =>
    let rule := pairQuotaRule K
    pathArcs (knownBudgetPath rule univ p (certifiedBudget rule univ p K.card) d)

theorem onePairQuotaArcs_subset (p : ℕ) (K : Arcs V) (D : List (V × V)) :
    onePairQuotaArcs p K D ⊆ K := by
  cases D with
  | nil => exact empty_subset _
  | cons d rest => exact pairQuotaPath_subset K p _ d

/-- The cost of choosing one quotient pair's path and normalizing its arcs. -/
def onePairQuotaArcWordBudget (n m q p : ℕ) : ℕ :=
  1 + ((m+1)*(quotaCertificateTrialWordBudget n m q p+15)+5 +
    (1+p*quotaTraceStepWordBudget n m q+(p+1)*quotaReplayStepWordBudget n m+6)+4) +
    2*(n*n^2)+12*n+3*m+9

theorem onePairQuotaArcWordBudget_mono_arcs (n q p : ℕ) :
    Monotone (fun m => onePairQuotaArcWordBudget n m q p) := by
  intro m M ordered
  dsimp only [onePairQuotaArcWordBudget, quotaCertificateTrialWordBudget, quotaTraceStepWordBudget,
    expensiveDemandWordBudget, quotaTrialWordBudget, quotaPurchaseWordBudget, quotaReplayStepWordBudget,
    quotaSelectionWordBudget, forwardStepWordBudget, reachInListWordBudget]
  gcongr

theorem onePairQuotaArcWordBudget_mono_quota (n m q : ℕ) :
    Monotone (onePairQuotaArcWordBudget n m q) := by
  intro p P ordered
  unfold onePairQuotaArcWordBudget quotaCertificateTrialWordBudget
  gcongr

def onePairQuotaArcsWithWordWork (Q : List (V × V)) (p : ℕ) (K : List (V × V)) (depth : ℕ) :
    List (V × V) → List (V × V) × ℕ
  | [] => ([],1)
  | d::_ =>
    let cap := K.length
    let chosen := certifiedQuotaPathWithWordWork K Q depth p cap d
    let edges := chosen.1.getD []
    let distinct := insertListWithChecks edges []
    (distinct.1,chosen.2+2*distinct.2+12*edges.length+3*cap+9)

theorem onePairQuotaArcsWithWordWork_spec (Q : List (V × V)) (p : ℕ) (K D : List (V × V))
    (complete : Q.toFinset = univ) (simple : K.Nodup) :
    let n := Fintype.card V
    let out := onePairQuotaArcsWithWordWork Q p K n D
    out.1.Nodup ∧ out.1.toFinset = onePairQuotaArcs p K.toFinset D ∧
      out.2 ≤ onePairQuotaArcWordBudget n K.length Q.length p := by
  cases D with
  | nil => simp [onePairQuotaArcsWithWordWork, onePairQuotaArcs, onePairQuotaArcWordBudget]
  | cons d rest =>
    let n := Fintype.card V
    let chosen := certifiedQuotaPathWithWordWork K Q n p K.length d
    let edges := chosen.1.getD []
    let distinct := insertListWithChecks edges []
    obtain ⟨same, cost⟩ := certifiedQuotaPathWithWordWork_spec K Q p K.length d
    have chosenEq : chosen.1 = knownBudgetPath (pairQuotaRule K.toFinset) univ p
        (certifiedBudget (pairQuotaRule K.toFinset) univ p K.toFinset.card) d := by
      change chosen.1 = _ at same
      rw [same, complete, ← List.toFinset_card_of_nodup simple]
      rfl
    obtain ⟨nodup, union, charged⟩ := insertListWithChecks_spec edges ([] : List (V × V)) List.nodup_nil
    have edgeLen : edges.length ≤ n := by
      change (chosen.1.getD []).length ≤ n
      rw [chosenEq]
      exact pairQuotaPath_length K.toFinset p _ d
    have normBound : distinct.2 ≤ n*n^2 := by
      apply charged.trans
      rw [Fintype.card_prod, ← pow_two]
      exact Nat.mul_le_mul_right _ edgeLen
    refine ⟨nodup, ?_, ?_⟩
    · change distinct.1.toFinset = _
      rw [union]
      simp only [List.toFinset_nil, empty_union, edges, chosenEq, onePairQuotaArcs, pathArcs]
    · change chosen.2+2*distinct.2+12*edges.length+3*K.length+9 ≤ _
      unfold onePairQuotaArcWordBudget
      have add := Nat.add_le_add_right (Nat.add_le_add_right
        (Nat.add_le_add (Nat.add_le_add cost (Nat.mul_le_mul_left 2 normBound))
          (Nat.mul_le_mul_left 12 edgeLen)) (3*K.length)) 9
      exact add.trans (by dsimp only [n]; omega)

end QuotientSelection

end OnlineReachabilityPreservers
