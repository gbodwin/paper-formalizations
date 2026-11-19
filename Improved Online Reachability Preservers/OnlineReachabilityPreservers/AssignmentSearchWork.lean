import OnlineReachabilityPreservers.AlgorithmSearchWork
import OnlineReachabilityPreservers.PairwiseNonAdaptive
import OnlineReachabilityPreservers.RestrictedNonAdaptive

/-! Compose base path work with quota certification and the lift of a fixed assignment. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V : Type*} [LinearOrder V] [Fintype V]

private def assignmentRule (K : Arcs V) : PathRule V :=
  fun A d => forwardPath K A d.1 d.2

private def assignmentRouteBound (n m : ℕ) : ℕ :=
  m*(2*((n+1)*n*m))+n*m+2*n^2

/-- One graph projection and demand, at most all quotient pairs in the lift, the
connector searches, and the original-graph shortest route of the selected path. -/
def assignmentLiftSearchBound (n m : ℕ) : ℕ :=
  (4*m+2+2*m*n^2+2*n)*(2*n*m)+2*n*((n+1)*n*m+n*m)+assignmentRouteBound n m

def assignmentSearchBound (n m q certCalls : ℕ) : ℕ :=
  assignmentLiftSearchBound n m +
    (certCalls+q*(n^2+1)+(q+1))*(n*m+2*n^2)

private def meteredAssignment (G K : Arcs V) (Q : Arcs V) (q : ℕ) (budget : ℕ × ℕ)
    (d : V × V) : Option (List (V × V)) × ℕ :=
  let n := Fintype.card V
  let m := G.card
  let selected := knownBudgetPathWithChoiceCalls (assignmentRule K) Q q budget.1 (projectDemand G d)
  let H := connectors G ∪ liftedArcs G (pathArcs selected.1)
  let routed := routePathWithSearchWork H d.1 d.2
  (routed.1, (4*m+2+2*m*(pathArcs selected.1).card+2*n)*(2*n*m)+
    2*n*((n+1)*n*m+n*m)+(routed.2.1+routed.2.2)+(budget.2+selected.2)*(n*m+2*n^2))

private theorem meteredAssignment_spec (G K : Arcs V) (Q : Arcs V) (q : ℕ) (budget : ℕ × ℕ)
    (d : V × V) :
    let out := meteredAssignment G K Q q budget d
    out.1 = liftPath G d (knownBudgetPath (assignmentRule K) Q q budget.1 (projectDemand G d)) ∧
      out.2 ≤ assignmentSearchBound (Fintype.card V) G.card q budget.2 := by
  let n := Fintype.card V
  let m := G.card
  let selected := knownBudgetPathWithChoiceCalls (assignmentRule K) Q q budget.1 (projectDemand G d)
  let A := pathArcs selected.1
  let H := connectors G ∪ liftedArcs G A
  let route := routePathWithSearchWork H d.1 d.2
  obtain ⟨path, calls⟩ := knownBudgetPathWithChoiceCalls_spec (assignmentRule K) Q q budget.1 (projectDemand G d)
  obtain ⟨routeEq, arcs, tests⟩ := routePathWithSearchWork_spec H d.1 d.2
  have bound (B : Arcs V) : B.card ≤ n^2 := by
    simpa only [Fintype.card_prod, pow_two] using card_le_univ B
  have hc : H.card ≤ m := card_le_card (union_subset (connectors_subset G) (liftedArcs_subset G A))
  have routeWork : route.2.1+route.2.2 ≤ assignmentRouteBound n m := by
    refine Nat.add_le_add (arcs.trans ?_) tests
    gcongr
  change route.1 = _ ∧ _
  refine ⟨routeEq.trans ?_, ?_⟩
  · unfold liftPath H A
    rw [show selected.1 = _ from path]
  · unfold assignmentSearchBound assignmentLiftSearchBound
    change (4*m+2+2*m*A.card+2*n)*(2*n*m)+2*n*((n+1)*n*m+n*m)+
      (route.2.1+route.2.2)+(budget.2+selected.2)*(n*m+2*n^2) ≤ _
    have charge : selected.2 ≤ q*(n^2+1)+(q+1) := calls.trans (by
      gcongr
      exact bound Q)
    have step : (budget.2+selected.2)*(n*m+2*n^2) ≤
        (budget.2+q*(n^2+1)+(q+1))*(n*m+2*n^2) := by
      rw [Nat.add_assoc budget.2]
      exact Nat.mul_le_mul_right _ (Nat.add_le_add_left charge _)
    exact Nat.add_le_add (Nat.add_le_add (by gcongr; exact bound A) routeWork) step

/-- The pairwise certification searches at most one candidate per possible budget,
then executes the chosen quota once. -/
def pairwiseAssignmentSearchBound (n m q : ℕ) : ℕ :=
  assignmentSearchBound n m q ((m+1)*(q*(n^2+1)+q))

private theorem pairwiseAssignmentSearchBound_mono (n m : ℕ) :
    Monotone (pairwiseAssignmentSearchBound n m) := by
  intro q Q le
  unfold pairwiseAssignmentSearchBound assignmentSearchBound
  gcongr

def knownPairPathWithSearchWork (G : Arcs V) (p : ℕ) (d : V × V) :
    Option (List (V × V)) × ℕ :=
  let K := condensation G
  let budget := certifiedBudgetWithChoiceCalls (assignmentRule K) univ p K.card
  meteredAssignment G K univ p budget d

theorem knownPairPathWithSearchWork_spec (G : Arcs V) (p : ℕ) (d : V × V) :
    let out := knownPairPathWithSearchWork G p d
    out.1 = knownPairPath G p d ∧
      out.2 ≤ pairwiseAssignmentSearchBound (Fintype.card V) G.card p := by
  let K := condensation G
  let n := Fintype.card V
  let budget := certifiedBudgetWithChoiceCalls (assignmentRule K) univ p K.card
  obtain ⟨same, calls⟩ := certifiedBudgetWithChoiceCalls_spec (assignmentRule K) univ p K.card
  obtain ⟨path, work⟩ := meteredAssignment_spec G K univ p budget d
  have card : K.card ≤ G.card := card_image_le.trans (card_le_card (filter_subset _ _))
  have bound : budget.2 ≤ (G.card+1)*(p*(n^2+1)+p) := calls.trans (by
    simp only [card_univ, Fintype.card_prod, pow_two]
    gcongr)
  refine ⟨path.trans ?_, work.trans ?_⟩
  · unfold knownPairPath
    rw [show budget.1 = _ from same]
    rfl
  · unfold pairwiseAssignmentSearchBound assignmentSearchBound
    gcongr

/-- A common upper bound on either dyadic schedule's selected quota. -/
def indexedSearchQuota (n i : ℕ) : ℕ := n+1+2*(i+1)

private theorem indexedSearchQuota_le {base n i : ℕ} (pos : 0 < base) (small : base ≤ n+1) :
    dyadicQuota base (indexLevel base i) ≤ indexedSearchQuota n i := by
  have h := finalQuota_le (base := base) (p := i+1) pos (Nat.succ_pos i)
  refine (by simpa using h : dyadicQuota base (indexLevel base i) ≤ max base (2*(i+1))).trans ?_
  exact max_le (small.trans (Nat.le_add_right _ _)) (Nat.le_add_left _ _)

def indexedPairPathWithSearchWork (G : Arcs V) (i : ℕ) (d : V × V) :
    Option (List (V × V)) × ℕ :=
  let base := pairwiseBase (Fintype.card V)
  knownPairPathWithSearchWork G (dyadicQuota base (indexLevel base i)) d

theorem indexedPairPathWithSearchWork_spec (G : Arcs V) (i : ℕ) (d : V × V) :
    let out := indexedPairPathWithSearchWork G i d
    out.1 = indexedPairPath G i d ∧
      out.2 ≤ pairwiseAssignmentSearchBound (Fintype.card V) G.card (indexedSearchQuota (Fintype.card V) i) := by
  let n := Fintype.card V
  let base := pairwiseBase n
  let q := dyadicQuota base (indexLevel base i)
  obtain ⟨path, work⟩ := knownPairPathWithSearchWork_spec G q d
  have cap : q ≤ indexedSearchQuota n i := indexedSearchQuota_le (by simp [base, pairwiseBase])
    (Nat.succ_le_succ (Nat.sqrt_le_self n))
  exact ⟨path, work.trans (pairwiseAssignmentSearchBound_mono n G.card cap)⟩

/-- Restricted assignments project each allowed sink and use the stated integer budget. -/
def restrictedAssignmentSearchBound (n m q : ℕ) : ℕ :=
  assignmentSearchBound n m q 0+n*(2*n*m)

private theorem restrictedAssignmentSearchBound_mono (n m : ℕ) :
    Monotone (restrictedAssignmentSearchBound n m) := by
  intro q Q le
  unfold restrictedAssignmentSearchBound assignmentSearchBound
  gcongr

def knownSinkPathWithSearchWork (G : Arcs V) (S : Finset V) (p : ℕ) (d : V × V) :
    Option (List (V × V)) × ℕ :=
  let n := Fintype.card V
  let Q := univ ×ˢ S.image (componentLabel G)
  let out := meteredAssignment G (condensation G) Q p (endpointBudget n S.card p,0) d
  (out.1, out.2+S.card*(2*n*G.card))

theorem knownSinkPathWithSearchWork_spec (G : Arcs V) (S : Finset V) (p : ℕ) (d : V × V) :
    let out := knownSinkPathWithSearchWork G S p d
    out.1 = knownSinkPath G S p d ∧
      out.2 ≤ restrictedAssignmentSearchBound (Fintype.card V) G.card p := by
  have result := meteredAssignment_spec G (condensation G) (univ ×ˢ S.image (componentLabel G)) p
    (endpointBudget (Fintype.card V) S.card p,0) d
  exact ⟨result.1, Nat.add_le_add result.2 (Nat.mul_le_mul_right _ (card_le_univ _))⟩

def indexedSinkPathWithSearchWork (G : Arcs V) (S : Finset V) (i : ℕ) (d : V × V) :
    Option (List (V × V)) × ℕ :=
  let base := endpointBase (Fintype.card V) S.card
  knownSinkPathWithSearchWork G S (dyadicQuota base (indexLevel base i)) d

theorem indexedSinkPathWithSearchWork_spec (G : Arcs V) (S : Finset V) (i : ℕ) (d : V × V) :
    let out := indexedSinkPathWithSearchWork G S i d
    out.1 = indexedSinkPath G S i d ∧
      out.2 ≤ restrictedAssignmentSearchBound (Fintype.card V) G.card (indexedSearchQuota (Fintype.card V) i) := by
  let n := Fintype.card V
  let base := endpointBase n S.card
  let q := dyadicQuota base (indexLevel base i)
  obtain ⟨path, work⟩ := knownSinkPathWithSearchWork_spec G S q d
  have cap : q ≤ indexedSearchQuota n i := indexedSearchQuota_le
    (Nat.zero_lt_one.trans_le (le_max_left _ _))
    (max_le (Nat.le_add_left _ _) ((Nat.div_le_self _ _).trans (Nat.le_succ _)))
  exact ⟨path, work.trans (restrictedAssignmentSearchBound_mono n G.card cap)⟩

def knownSourcePathWithSearchWork (G : Arcs V) (S : Finset V) (p : ℕ) (d : V × V) :
    Option (List (V × V)) × ℕ :=
  let out := knownSinkPathWithSearchWork (reverseArcs G) S p d.swap
  (reversePath out.1, out.2)

theorem knownSourcePathWithSearchWork_spec (G : Arcs V) (S : Finset V) (p : ℕ) (d : V × V) :
    let out := knownSourcePathWithSearchWork G S p d
    out.1 = knownSourcePath G S p d ∧
      out.2 ≤ restrictedAssignmentSearchBound (Fintype.card V) G.card p := by
  obtain ⟨same, work⟩ := knownSinkPathWithSearchWork_spec (reverseArcs G) S p d.swap
  exact ⟨congrArg reversePath same, by simpa only [knownSourcePathWithSearchWork, reverseArcs_card] using work⟩

def indexedSourcePathWithSearchWork (G : Arcs V) (S : Finset V) (i : ℕ) (d : V × V) :
    Option (List (V × V)) × ℕ :=
  let out := indexedSinkPathWithSearchWork (reverseArcs G) S i d.swap
  (reversePath out.1, out.2)

theorem indexedSourcePathWithSearchWork_spec (G : Arcs V) (S : Finset V) (i : ℕ) (d : V × V) :
    let out := indexedSourcePathWithSearchWork G S i d
    out.1 = indexedSourcePath G S i d ∧
      out.2 ≤ restrictedAssignmentSearchBound (Fintype.card V) G.card (indexedSearchQuota (Fintype.card V) i) := by
  obtain ⟨same, work⟩ := indexedSinkPathWithSearchWork_spec (reverseArcs G) S i d.swap
  exact ⟨congrArg reversePath same, by simpa only [indexedSourcePathWithSearchWork, reverseArcs_card] using work⟩

/-- Evaluate each indexed assignment once and compute its ordinary path union. -/
def plannedArcsWithSearchWork (choose : ℕ → V × V → Option (List (V × V)) × ℕ)
    (D : List (V × V)) : Arcs V × ℕ :=
  let row : Fin D.length ↪ Fin D.length × (Option (List (V × V)) × ℕ) :=
    ⟨fun i => (i,choose i.val (D.get i)), fun _ _ equal => congrArg Prod.fst equal⟩
  let picked := univ.map row
  (picked.biUnion (fun r => pathArcs r.2.1), ∑ r ∈ picked, r.2.2)

omit [Fintype V] in
theorem plannedArcsWithSearchWork_spec (choose : ℕ → V × V → Option (List (V × V)) × ℕ)
    (plain : ℕ → V × V → Option (List (V × V))) (D : List (V × V)) (bound : ℕ)
    (same : ∀ i : Fin D.length, (choose i.val (D.get i)).1 = plain i.val (D.get i))
    (work : ∀ i : Fin D.length, (choose i.val (D.get i)).2 ≤ bound) :
    let out := plannedArcsWithSearchWork choose D
    out.1 = plannedArcs plain D ∧ out.2 ≤ D.length*bound := by
  constructor
  · ext e
    simp only [plannedArcsWithSearchWork, plannedArcs, mem_biUnion, mem_map, mem_univ, true_and]
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, hi⟩
      exact ⟨i, same i ▸ hi⟩
    · rintro ⟨i, hi⟩
      exact ⟨_, ⟨i, rfl⟩, (same i).symm ▸ hi⟩
  · simp only [plannedArcsWithSearchWork, sum_map]
    calc
      _ ≤ ∑ _ : Fin D.length, bound := sum_le_sum fun i _ => work i
      _ = _ := by simp

theorem indexedPairPreserverWithSearchWork_spec (G : Arcs V) (D : List (V × V)) :
    let out := plannedArcsWithSearchWork (indexedPairPathWithSearchWork G) D
    out.1 = plannedArcs (indexedPairPath G) D ∧ out.2 ≤ D.length*
      pairwiseAssignmentSearchBound (Fintype.card V) G.card (indexedSearchQuota (Fintype.card V) D.length) := by
  apply plannedArcsWithSearchWork_spec
  · intro i
    exact (indexedPairPathWithSearchWork_spec G i.val (D.get i)).1
  · intro i
    refine (indexedPairPathWithSearchWork_spec G i.val (D.get i)).2.trans
      (pairwiseAssignmentSearchBound_mono _ _ ?_)
    unfold indexedSearchQuota
    gcongr
    exact i.isLt.le

end OnlineReachabilityPreservers
