import OnlineReachabilityPreservers.AssignmentListPairwiseWork
import OnlineReachabilityPreservers.DeterministicEnumerationWork

/-! Accumulate the exact assigned-path union at each arrival, charging list work. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V : Type*} [LinearOrder V]

private theorem plannedArcs_cons_offset (choose : ℕ → V × V → Option (List (V × V)))
    (i : ℕ) (d : V × V) (D : List (V × V)) :
    plannedArcs (fun j => choose (i+j)) (d::D) =
      pathArcs (choose i d) ∪ plannedArcs (fun j => choose (i+1+j)) D := by
  ext e
  simp only [plannedArcs, mem_biUnion, mem_univ, true_and, mem_union]
  constructor
  · rintro ⟨j, on⟩
    cases j using Fin.cases with
    | zero => exact Or.inl (by simpa using on)
    | succ j =>
      refine Or.inr ⟨j, ?_⟩
      change e ∈ pathArcs (choose (i+(j.val+1)) (D.get j)) at on
      rw [show i+1+j.val = i+(j.val+1) by omega]
      exact on
  · rintro (on | ⟨j,on⟩)
    · exact ⟨0, by simpa using on⟩
    · refine ⟨j.succ, ?_⟩
      change e ∈ pathArcs (choose (i+(j.val+1)) (D.get j))
      rw [show i+(j.val+1) = i+1+j.val by omega]
      exact on

private def assignmentPrefixesFromWithWordWork
    (choose : ℕ → V × V → Option (List (V × V)) × ℕ) :
    ℕ → List (V × V) → List (V × V) → List (List (V × V)) × ℕ
  | _, [], H => ([H],3)
  | i, d::ds, H =>
    let chosen := choose i d
    let edges := chosen.1.getD []
    let purchased := insertListWithChecks edges H
    let suffix := assignmentPrefixesFromWithWordWork choose (i+1) ds purchased.1
    (H::suffix.1, chosen.2+2*purchased.2+12*edges.length+suffix.2+12)

/-- Select each requested path once and return the accumulated edge list
at the empty prefix and after each arrival. Insertion reuses the previously
selected arc list and the tally charges the path-list traversal and key tests. -/
def assignmentPrefixesWithWordWork
    (choose : ℕ → V × V → Option (List (V × V)) × ℕ) (D : List (V × V)) :
    List (List (V × V)) × ℕ :=
  assignmentPrefixesFromWithWordWork choose 0 D []

/-- Source-level word tally for a sequence of bounded path queries and
duplicate-free insertions. -/
def assignmentPrefixesWordBudget (n p query : ℕ) : ℕ :=
  3+p*(query+2*(n*n^2)+12*n+12)

variable [Fintype V]

private theorem assignmentPrefixesFromWithWordWork_spec
    (choose : ℕ → V × V → Option (List (V × V)) × ℕ)
    (plain : ℕ → V × V → Option (List (V × V)))
    (same : ∀ i d, (choose i d).1 = plain i d)
    (short : ∀ i d, ((plain i d).getD []).length ≤ Fintype.card V)
    (query i : ℕ) (D H : List (V × V)) (simple : H.Nodup)
    (cost : ∀ j : Fin D.length, (choose (i+j) (D.get j)).2 ≤ query) :
    let out := assignmentPrefixesFromWithWordWork choose i D H
    (∀ A ∈ out.1, List.Nodup A) ∧
      out.1.map List.toFinset = D.inits.map (fun P => H.toFinset ∪ plannedArcs (fun j => plain (i+j)) P) ∧
      out.2 ≤ assignmentPrefixesWordBudget (Fintype.card V) D.length query := by
  dsimp only
  induction D generalizing i H with
  | nil => simp [assignmentPrefixesFromWithWordWork, plannedArcs, assignmentPrefixesWordBudget, simple]
  | cons d D ih =>
    let n := Fintype.card V
    let chosen := choose i d
    let edges := chosen.1.getD []
    let purchased := insertListWithChecks edges H
    let suffix := assignmentPrefixesFromWithWordWork choose (i+1) D purchased.1
    obtain ⟨boughtSimple, boughtSet, boughtWork⟩ := insertListWithChecks_spec edges H simple
    have bought : purchased.1.toFinset = H.toFinset ∪ pathArcs (plain i d) := by
      apply boughtSet.trans
      simp only [edges, chosen, same, pathArcs]
    have queryNow : chosen.2 ≤ query := by simpa using cost 0
    have queryRest (j : Fin D.length) : (choose (i+1+j) (D.get j)).2 ≤ query := by
      have h := cost j.succ
      change (choose (i+(j.val+1)) (D.get j)).2 ≤ query at h
      rw [show i+1+j.val = i+(j.val+1) by omega]
      exact h
    obtain ⟨simpleRest, restSet, restWork⟩ := ih (i+1) purchased.1 boughtSimple queryRest
    have shortNow : edges.length ≤ n := by
      simp only [edges, chosen, same]
      exact short i d
    have insertCost : purchased.2 ≤ n*n^2 := by
      apply boughtWork.trans
      rw [Fintype.card_prod, ← pow_two]
      exact Nat.mul_le_mul_right _ shortNow
    refine ⟨?_, ?_, ?_⟩
    · change ∀ A ∈ H::suffix.1, List.Nodup A
      intro A member
      rcases List.mem_cons.mp member with rfl | on
      · exact simple
      · exact simpleRest _ on
    · change H.toFinset :: suffix.1.map List.toFinset = _
      rw [show suffix.1.map List.toFinset = _ from restSet]
      rw [List.inits_cons, List.map_cons, List.map_map]
      have empty : plannedArcs (fun j => plain (i+j)) [] = ∅ := by simp [plannedArcs]
      rw [empty, union_empty]
      congr 1
      apply List.map_congr_left
      intro P _
      rw [bought, Function.comp_apply, plannedArcs_cons_offset, union_assoc]
    · change chosen.2+2*purchased.2+12*edges.length+suffix.2+12 ≤ _
      calc
        _ ≤ query+2*(n*n^2)+12*n+assignmentPrefixesWordBudget n D.length query+12 := by gcongr
        _ = assignmentPrefixesWordBudget n (d::D).length query := by
          simp only [assignmentPrefixesWordBudget, List.length_cons]
          ring

theorem assignmentPrefixesWithWordWork_spec
    (choose : ℕ → V × V → Option (List (V × V)) × ℕ)
    (plain : ℕ → V × V → Option (List (V × V)))
    (same : ∀ i d, (choose i d).1 = plain i d)
    (short : ∀ i d, ((plain i d).getD []).length ≤ Fintype.card V)
    (query : ℕ) (D : List (V × V))
    (cost : ∀ j : Fin D.length, (choose j (D.get j)).2 ≤ query) :
    let out := assignmentPrefixesWithWordWork choose D
    (∀ A ∈ out.1, List.Nodup A) ∧
      out.1.map List.toFinset = D.inits.map (plannedArcs plain) ∧
      out.2 ≤ assignmentPrefixesWordBudget (Fintype.card V) D.length query := by
  simpa only [assignmentPrefixesWithWordWork, List.toFinset_nil, empty_union, zero_add]
    using assignmentPrefixesFromWithWordWork_spec choose plain same short query 0 D [] List.nodup_nil
      (fun j => by simpa only [zero_add] using cost j)

/-- The selected lift is simple even when the quotient option is absent. -/
theorem liftPath_length_le (G : Arcs V) (d : V × V) (p : Option (List (V × V))) :
    ((liftPath G d p).getD []).length ≤ Fintype.card V := by
  unfold liftPath
  cases chosen : routePath (connectors G ∪ liftedArcs G (pathArcs p)) d.1 d.2 with
  | none => simp
  | some path =>
    have distinct := (routePath_some chosen).2
    have bound := card_le_univ (path.map Prod.fst ++ [d.2]).toFinset
    rw [List.toFinset_card_of_nodup distinct, List.length_append, List.length_map, List.length_singleton] at bound
    exact (Nat.le_succ _).trans bound

/-- Bound the computation of one indexed pairwise path, including its
square-root base and least dyadic quota. -/
def indexedPairQueryWordBudget (n m i : ℕ) : ℕ :=
  (20*(n+1)+5)+(1+6*(i+1))+knownPairPathWordBudget n m (n+1+2*(i+1))+3*n+10

private theorem indexedPairQueryWordBudget_mono_index (n m : ℕ) :
    Monotone (indexedPairQueryWordBudget n m) := by
  intro a b less
  have caps : n+1+2*(a+1) ≤ n+1+2*(b+1) := by gcongr
  have quota := onePairQuotaArcWordBudget_mono_quota n m (n^2) caps
  unfold indexedPairQueryWordBudget knownPairPathWordBudget
  gcongr

/-- All prefix edge sets of the assignment that knows the total. The
evaluation executes one exact path query on each arrival. -/
theorem knownPairAssignmentPrefixesWithWordWork_spec (G : List (V × V))
    (vertices : List V) (p : ℕ) (D : List (V × V))
    (unique : vertices.Nodup) (complete : ∀ v : V, v ∈ vertices) :
    let n := Fintype.card V
    let choose := fun _ => knownPairPathWithWordWork G vertices p
    let out := assignmentPrefixesWithWordWork choose D
    (∀ A ∈ out.1, List.Nodup A) ∧
      out.1.map List.toFinset = D.inits.map (plannedArcs (fun _ => knownPairPath G.toFinset p)) ∧
      out.2 ≤ assignmentPrefixesWordBudget n D.length (knownPairPathWordBudget n G.length p) :=
  assignmentPrefixesWithWordWork_spec _ _
    (fun _ d => (knownPairPathWithWordWork_spec G vertices p d unique complete).1)
    (fun _ d => by unfold knownPairPath; exact liftPath_length_le _ _ _)
    _ D (fun j => (knownPairPathWithWordWork_spec G vertices p (D.get j) unique complete).2)

/-- All prefix edge sets of the assignment that only knows the arrival
index. Earlier selected lists are retained as later edges are inserted. -/
theorem indexedPairAssignmentPrefixesWithWordWork_spec (G : List (V × V))
    (vertices : List V) (D : List (V × V))
    (unique : vertices.Nodup) (complete : ∀ v : V, v ∈ vertices) :
    let n := Fintype.card V
    let out := assignmentPrefixesWithWordWork (indexedPairPathWithWordWork G vertices) D
    (∀ A ∈ out.1, List.Nodup A) ∧
      out.1.map List.toFinset = D.inits.map (plannedArcs (indexedPairPath G.toFinset)) ∧
      out.2 ≤ assignmentPrefixesWordBudget n D.length (indexedPairQueryWordBudget n G.length D.length) :=
  assignmentPrefixesWithWordWork_spec _ _
    (fun i d => (indexedPairPathWithWordWork_spec G vertices i d unique complete).1)
    (fun _ d => by unfold indexedPairPath; exact liftPath_length_le _ _ _)
    _ D (fun j =>
      (indexedPairPathWithWordWork_spec G vertices j (D.get j) unique complete).2.trans
        (indexedPairQueryWordBudget_mono_index _ _ j.isLt.le))

/-- For indexed vertices, include one complete enumeration in the cost of
all prefixes of the known-total assignment. -/
theorem knownPairFinAssignmentPrefixesWithWordWork_spec {n : ℕ}
    (G : List (Fin n × Fin n)) (p : ℕ) (D : List (Fin n × Fin n)) :
    let out := withFinVerticesWithWordWork
      (fun vertices => assignmentPrefixesWithWordWork (fun _ => knownPairPathWithWordWork G vertices p) D)
    out.1.map List.toFinset = D.inits.map (plannedArcs (fun _ => knownPairPath G.toFinset p)) ∧
      out.2 ≤ 8*n+1+assignmentPrefixesWordBudget n D.length (knownPairPathWordBudget n G.length p)+4 := by
  refine withFinVerticesWithWordWork_spec
    (P := fun (lists : List (List (Fin n × Fin n))) => lists.map List.toFinset =
      D.inits.map (plannedArcs (fun _ => knownPairPath G.toFinset p))) _ _ ?_
  intro vertices unique complete
  simpa only [Fintype.card_fin] using
    (knownPairAssignmentPrefixesWithWordWork_spec G vertices p D unique complete).2

/-- For indexed vertices, include one complete enumeration in the cost of
all prefixes of the arrival-index assignment. -/
theorem indexedPairFinAssignmentPrefixesWithWordWork_spec {n : ℕ}
    (G D : List (Fin n × Fin n)) :
    let out := withFinVerticesWithWordWork
      (fun vertices => assignmentPrefixesWithWordWork (indexedPairPathWithWordWork G vertices) D)
    out.1.map List.toFinset = D.inits.map (plannedArcs (indexedPairPath G.toFinset)) ∧
      out.2 ≤ 8*n+1+assignmentPrefixesWordBudget n D.length (indexedPairQueryWordBudget n G.length D.length)+4 := by
  refine withFinVerticesWithWordWork_spec
    (P := fun (lists : List (List (Fin n × Fin n))) =>
      lists.map List.toFinset = D.inits.map (plannedArcs (indexedPairPath G.toFinset))) _ _ ?_
  intro vertices unique complete
  simpa only [Fintype.card_fin] using
    (indexedPairAssignmentPrefixesWithWordWork_spec G vertices D unique complete).2

end OnlineReachabilityPreservers
