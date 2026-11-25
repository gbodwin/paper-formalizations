import OnlineReachabilityPreservers.AssignmentListQuotaWork
import OnlineReachabilityPreservers.AssignmentListRouteWork
import OnlineReachabilityPreservers.AssignmentQuotaArithmeticWork
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
  let root := natSqrtWithWordWork n
  (root.1+1,root.2)

private theorem pairwiseBaseWithWordWork_spec (n : ℕ) :
    let out := pairwiseBaseWithWordWork n
    out.1 = pairwiseBase n ∧ out.2 ≤ 20*(n+1)+5 := by
  obtain ⟨root, cost⟩ := natSqrtWithWordWork_spec n
  exact ⟨congrArg (· + 1) root, cost⟩

/-- The pairwise assignment for an arrival index. The dyadic quota is
computed by doubling until the request count is covered. -/
def indexedPairPathWithWordWork (G : List (V × V)) (vertices : List V) (i : ℕ) (d : V × V) :
    Option (List (V × V)) × ℕ :=
  let n := vertices.length
  let base := pairwiseBaseWithWordWork n
  let quota := indexQuotaWithWordWork base.1 i
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
  let quota := indexQuotaWithWordWork base.1 i
  obtain ⟨baseEq,baseWork⟩ := pairwiseBaseWithWordWork_spec n
  have positive : 0 < pairwiseBase n := Nat.succ_pos _
  have basePos : 0 < base.1 := by rw [baseEq]; exact positive
  obtain ⟨quotaEq, quotaWork⟩ := indexQuotaWithWordWork_spec base.1 i basePos
  have target : quota.1 = dyadicQuota (pairwiseBase n) (indexLevel (pairwiseBase n) i) := by
    rw [show quota.1 = _ from quotaEq, baseEq]
  have small : quota.1 ≤ n+1+2*(i+1) := by
    rw [target]
    have baseSmall : pairwiseBase n ≤ n+1 := Nat.succ_le_succ (Nat.sqrt_le_self n)
    exact (indexQuota_le_add positive i).trans (Nat.add_le_add_right baseSmall _)
  obtain ⟨path,work⟩ := knownPairPathWithWordWork_spec G vertices quota.1 d unique complete
  have pathWork := work.trans (knownPairPathWordBudget_mono_quota n G.length small)
  dsimp only [indexedPairPathWithWordWork]
  rw [count]
  change (knownPairPathWithWordWork G vertices quota.1 d).1 = _ ∧
    base.2+quota.2+(knownPairPathWithWordWork G vertices quota.1 d).2+3*n+10 ≤ _
  refine ⟨?_, Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add baseWork quotaWork) pathWork) _) _⟩
  rw [path,target]
  rfl

end OnlineReachabilityPreservers
