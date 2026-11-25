import OnlineReachabilityPreservers.AssignmentListQuotaWork
import OnlineReachabilityPreservers.AssignmentListRouteWork
import OnlineReachabilityPreservers.PairwiseNonAdaptive

/-! Source-level operation counts for one pairwise path assignment in both models of Theorem 5. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V : Type*} [LinearOrder V] [Fintype V]

/-- Find one path in the known-total pairwise assignment. Build the candidate
domain, select the quotient path, lift it and route through its allowed arcs. -/
def knownPairPathWithWordWork (G : List (V × V)) (vertices : List V) (p : ℕ) (d : V × V) :
    Option (List (V × V)) × ℕ :=
  let candidates := vertices ×ˢ vertices
  let lifted := liftCoreListWithWordWork (onePairQuotaArcsWithWordWork candidates p) G vertices [d]
  let n := vertices.length
  let routed := routePathListWithWordWork lifted.1 d.1 d.2 n
  (routed.1, lifted.2+routed.2+18*n^2+14*n+20)

def knownPairPathWordBudget (n m p : ℕ) : ℕ :=
  (1+liftCoreWordBudget n m 1+onePairQuotaArcWordBudget n m (n^2) p) +
    routePathListWordBudget n m+18*n^2+14*n+20

theorem knownPairPathWithWordWork_spec (G : List (V × V)) (vertices : List V) (p : ℕ) (d : V × V)
    (unique : vertices.Nodup) (complete : ∀ v : V, v ∈ vertices) :
    let n := Fintype.card V
    let m := G.length
    let out := knownPairPathWithWordWork G vertices p d
    out.1 = knownPairPath G.toFinset p d ∧ out.2 ≤ knownPairPathWordBudget n m p := by
  let n := Fintype.card V
  let candidates := vertices ×ˢ vertices
  let lifted := liftCoreListWithWordWork (onePairQuotaArcsWithWordWork candidates p) G vertices [d]
  let routed := routePathListWithWordWork lifted.1 d.1 d.2 vertices.length
  have cover : vertices.toFinset = univ := by ext v; simp [complete]
  have nVertices : vertices.length = n := by rw [← List.toFinset_card_of_nodup unique, cover, card_univ]
  have allPairs : candidates.toFinset = univ := by
    ext ⟨u,v⟩
    simp [candidates, complete]
  have cardPairs : candidates.length = n^2 := by
    simp only [candidates, List.length_product, nVertices, pow_two]
  obtain ⟨simpleLift, liftedSet, liftCost⟩ := liftCoreListWithWordWork_spec
    (onePairQuotaArcsWithWordWork candidates p) (onePairQuotaArcs p)
    (fun a b _ => onePairQuotaArcWordBudget a b candidates.length p)
    (fun K D simple => onePairQuotaArcsWithWordWork_spec candidates p K D allPairs simple)
    (onePairQuotaArcs_subset p) (fun a _ => onePairQuotaArcWordBudget_mono_arcs a candidates.length p)
    G vertices [d] unique complete
  have set : lifted.1.toFinset = liftedRun (onePairQuotaArcs p) G.toFinset [d] := liftedSet
  have sub : lifted.1.toFinset ⊆ G.toFinset := by
    rw [set]
    exact union_subset (connectors_subset _) (liftedArcs_subset _ _)
  have lenLift : lifted.1.length ≤ G.length := by
    rw [← List.toFinset_card_of_nodup simpleLift]
    exact (card_le_card sub).trans (List.toFinset_card_le _)
  obtain ⟨path, charge⟩ := routePathListWithWordWork_spec lifted.1 d.1 d.2
  have routeEq : routed.1 = routePath lifted.1.toFinset d.1 d.2 := by
    unfold routed
    rw [nVertices]
    exact path
  have routeCost : routed.2 ≤ routePathListWordBudget n G.length := by
    unfold routed
    rw [nVertices]
    exact charge.trans (routePathListWordBudget_mono_arcs n lenLift)
  have liftBound : lifted.2 ≤ 1+liftCoreWordBudget n G.length 1+onePairQuotaArcWordBudget n G.length (n^2) p := by
    simpa only [List.length_singleton, cardPairs] using liftCost
  constructor
  · change routed.1 = _
    rw [routeEq, set]
    rfl
  · change lifted.2+routed.2+18*vertices.length^2+14*vertices.length+20 ≤ _
    rw [nVertices]
    exact Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.add_le_add_right (Nat.add_le_add liftBound routeCost) (18*n^2)) (14*n)) 20

private theorem knownPairPathWordBudget_mono_quota (n m : ℕ) : Monotone (knownPairPathWordBudget n m) := by
  intro p P ordered
  unfold knownPairPathWordBudget
  have cost := onePairQuotaArcWordBudget_mono_quota n m (n^2) ordered
  gcongr

private def pairwiseBaseWithWordWork (n : ℕ) : ℕ × ℕ :=
  let found := leastWhereWithChecks (fun k => (decide (n < (k+1)^2),5)) (List.range (n+1))
  (found.1.getD n+1,found.2+14*(n+1)+5)

private theorem pairwiseBaseWithWordWork_spec (n : ℕ) :
    let out := pairwiseBaseWithWordWork n
    out.1 = pairwiseBase n ∧ out.2 ≤ 20*(n+1)+5 := by
  let P := fun k => n < (k+1)^2
  let keys := List.range (n+1)
  let domain := keys.toFinset.filter P
  obtain ⟨same, work⟩ := leastWhereWithChecks_spec (fun k => (decide (P k),5)) P keys 5
    (fun _ _ => rfl) (fun _ _ => le_rfl)
  have inside : n.sqrt ∈ domain := by
    apply mem_filter.mpr
    exact ⟨List.mem_toFinset.mpr (List.mem_range.mpr (Nat.lt_succ_of_le (Nat.sqrt_le_self n))), Nat.lt_succ_sqrt' n⟩
  obtain ⟨least, chosen⟩ := least?_some ⟨_,inside⟩
  have right : least ≤ n.sqrt := least?_le chosen inside
  have left : n.sqrt ≤ least := Nat.le_of_lt_succ
    (Nat.sqrt_lt'.mpr (mem_filter.mp (least?_mem chosen)).2)
  constructor
  · change (leastWhereWithChecks (fun k => (decide (P k),5)) keys).1.getD n + 1 = _
    rw [same, show keys.toFinset.filter P = domain from rfl, chosen, le_antisymm right left]
    rfl
  · change (leastWhereWithChecks (fun k => (decide (P k),5)) keys).2+14*(n+1)+5 ≤ _
    have len : keys.length = n+1 := List.length_range
    rw [len] at work
    exact (Nat.add_le_add_right (Nat.add_le_add_right work _) _).trans_eq (by ring)

private def coverByDoublingWithWordWork (needed : ℕ) : ℕ → ℕ → ℕ × ℕ
  | 0, quota => (quota,1)
  | steps+1, quota =>
    if needed ≤ quota then (quota,4)
    else
      let rest := coverByDoublingWithWordWork needed steps (2*quota)
      (rest.1,rest.2+6)

private theorem coverByDoublingWithWordWork_cost (needed fuel quota : ℕ) :
    (coverByDoublingWithWordWork needed fuel quota).2 ≤ 1+6*fuel := by
  induction fuel generalizing quota with
  | zero => simp [coverByDoublingWithWordWork]
  | succ k ih =>
    rw [coverByDoublingWithWordWork]
    split
    · change 4 ≤ 1+6*(k+1)
      omega
    · have bound := ih (2*quota)
      change (coverByDoublingWithWordWork needed k (2*quota)).2+6 ≤ 1+6*(k+1)
      omega

private theorem coverByDoublingWithWordWork_exact {base : ℕ} (positive : 0 < base) (i fuel level : ℕ)
    (before : level ≤ indexLevel base i) (enough : indexLevel base i ≤ level+fuel) :
    (coverByDoublingWithWordWork (i+1) fuel (dyadicQuota base level)).1 =
      dyadicQuota base (indexLevel base i) := by
  induction fuel generalizing level with
  | zero =>
    have exactLevel : level = indexLevel base i := le_antisymm before (by simpa using enough)
    simp [coverByDoublingWithWordWork, exactLevel]
  | succ k ih =>
    rw [coverByDoublingWithWordWork]
    split
    · rename_i covered
      have exactLevel : level = indexLevel base i := le_antisymm before (indexLevel_le_of_cover positive covered)
      rw [exactLevel]
    · rename_i missing
      have next : level+1 ≤ indexLevel base i := by
        apply Nat.succ_le_of_lt
        refine lt_of_le_of_ne before ?_
        intro equal
        exact missing (equal.symm ▸ indexLevel_covers positive i)
      have continued := ih (level+1) next (by omega)
      rw [dyadicQuota_succ] at continued
      exact continued

/-- The pairwise assignment for an arrival index. The dyadic quota is
computed by doubling until the request count is covered. -/
def indexedPairPathWithWordWork (G : List (V × V)) (vertices : List V) (i : ℕ) (d : V × V) :
    Option (List (V × V)) × ℕ :=
  let n := vertices.length
  let base := pairwiseBaseWithWordWork n
  let quota := coverByDoublingWithWordWork (i+1) (i+1) base.1
  let assigned := knownPairPathWithWordWork G vertices quota.1 d
  (assigned.1, base.2+quota.2+assigned.2+3*n+10)

theorem indexedPairPathWithWordWork_spec (G : List (V × V)) (vertices : List V) (i : ℕ) (d : V × V)
    (unique : vertices.Nodup) (complete : ∀ v : V, v ∈ vertices) :
    let n := Fintype.card V
    let out := indexedPairPathWithWordWork G vertices i d
    out.1 = indexedPairPath G.toFinset i d ∧
      out.2 ≤ (20*(n+1)+5)+(1+6*(i+1))+
        knownPairPathWordBudget n G.length (n+1+2*(i+1))+3*n+10 := by
  let n := Fintype.card V
  have cover : vertices.toFinset = univ := by ext v; simp [complete]
  have count : vertices.length = n := by rw [← List.toFinset_card_of_nodup unique, cover, card_univ]
  let base := pairwiseBaseWithWordWork n
  let quota := coverByDoublingWithWordWork (i+1) (i+1) base.1
  obtain ⟨baseEq,baseWork⟩ := pairwiseBaseWithWordWork_spec n
  have positive : 0 < pairwiseBase n := Nat.succ_pos _
  have feasible : indexLevel (pairwiseBase n) i ≤ 0+(i+1) :=
    (indexLevel_le_log2_succ positive i).trans (by have := Nat.log2_le_self i; omega)
  have target : quota.1 = dyadicQuota (pairwiseBase n) (indexLevel (pairwiseBase n) i) := by
    unfold quota
    rw [show base.1 = pairwiseBase n from baseEq]
    have solved := coverByDoublingWithWordWork_exact positive i (i+1) 0 (Nat.zero_le _) feasible
    simpa only [dyadicQuota, pow_zero, Nat.mul_one] using solved
  have small : quota.1 ≤ n+1+2*(i+1) := by
    rw [target]
    have bound := finalQuota_le positive (p := i+1) (Nat.succ_pos i)
    have baseSmall : pairwiseBase n ≤ n+1 := Nat.succ_le_succ (Nat.sqrt_le_self n)
    exact (by simpa only [Nat.add_sub_cancel] using bound :
      dyadicQuota (pairwiseBase n) (indexLevel (pairwiseBase n) i) ≤ max (pairwiseBase n) (2*(i+1))).trans
        (max_le (baseSmall.trans (Nat.le_add_right _ _)) (Nat.le_add_left _ _))
  obtain ⟨path,work⟩ := knownPairPathWithWordWork_spec G vertices quota.1 d unique complete
  have quotaWork := coverByDoublingWithWordWork_cost (i+1) (i+1) base.1
  have pathWork := work.trans (knownPairPathWordBudget_mono_quota n G.length small)
  dsimp only [indexedPairPathWithWordWork]
  rw [count]
  change (knownPairPathWithWordWork G vertices quota.1 d).1 = _ ∧
    base.2+quota.2+(knownPairPathWithWordWork G vertices quota.1 d).2+3*n+10 ≤ _
  refine ⟨?_, Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add baseWork quotaWork) pathWork) _) _⟩
  rw [path,target]
  rfl

end OnlineReachabilityPreservers
