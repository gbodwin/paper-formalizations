import OnlineReachabilityPreservers.DeterministicListWork
import OnlineReachabilityPreservers.OfflineIndependence
import OnlineReachabilityPreservers.SteinerSortWork

/-! Key comparisons in the greedy offline deletion rule. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V : Type*} [LinearOrder V] [Fintype V]

private def reachListWithChecks (arcs : List (V × V)) (d : V × V) : Bool × ℕ :=
  reachTestListWithChecks arcs d.1 d.2 (Fintype.card V)

private theorem reachListWithChecks_spec (arcs : List (V × V)) (d : V × V) :
    let n := Fintype.card V
    let out := reachListWithChecks arcs d
    out.1 = decide (d.1 ∈ reaches arcs.toFinset d.2) ∧
      out.2 ≤ n*(arcs.length*(2*n))+n :=
  reachTestListWithChecks_spec arcs d.1 d.2 (Fintype.card V)

private def servesListWithChecks (G H : List (V × V)) : List (V × V) → Bool × ℕ
  | [] => (true,0)
  | d::ds =>
    let needed := reachListWithChecks G d
    if needed.1 then
      let present := reachListWithChecks H d
      if present.1 then
        let tail := servesListWithChecks G H ds
        (tail.1, needed.2+present.2+tail.2)
      else (false,needed.2+present.2)
    else
      let tail := servesListWithChecks G H ds
      (tail.1,needed.2+tail.2)

def servesListBudget (n m : ℕ) : ℕ := 2*(n*(m*(2*n))+n)

private theorem servesListWithChecks_spec (G H D : List (V × V)) (small : H.length ≤ G.length) :
    let out := servesListWithChecks G H D
    out.1 = serves G.toFinset H.toFinset D ∧
      out.2 ≤ D.length*servesListBudget (Fintype.card V) G.length := by
  induction D with
  | nil => simp [servesListWithChecks, serves]
  | cons d ds ih =>
    let needed := reachListWithChecks G d
    let present := reachListWithChecks H d
    let tail := servesListWithChecks G H ds
    let n := Fintype.card V
    let budget := n*(G.length*(2*n))+n
    obtain ⟨Gtest,Gwork⟩ := reachListWithChecks_spec G d
    obtain ⟨Htest,Hwork⟩ := reachListWithChecks_spec H d
    have Hcost : present.2 ≤ budget := Hwork.trans (by dsimp only [budget]; gcongr)
    have Gcost : needed.2 ≤ budget := Gwork
    obtain ⟨tailEq,tailCost⟩ := ih
    have cost : needed.2+present.2+tail.2 ≤ (ds.length+1)*servesListBudget n G.length := by
      rw [Nat.succ_mul]
      have more : needed.2+present.2 ≤ servesListBudget n G.length := by
        simpa only [servesListBudget, two_mul, budget] using Nat.add_le_add Gcost Hcost
      exact (Nat.add_le_add more tailCost).trans_eq (add_comm _ _)
    have atMostPair := (Nat.le_add_right (needed.2+present.2) tail.2).trans cost
    have atMostOne := (Nat.add_le_add_right (Nat.le_add_right needed.2 present.2) tail.2).trans cost
    unfold servesListWithChecks
    dsimp only
    change (if needed.1 then (if present.1 then (tail.1, needed.2+present.2+tail.2)
      else (false,needed.2+present.2)) else (tail.1,needed.2+tail.2)).1 = _ ∧
      (if needed.1 then (if present.1 then (tail.1, needed.2+present.2+tail.2)
        else (false,needed.2+present.2)) else (tail.1,needed.2+tail.2)).2 ≤ _
    change needed.1 = _ at Gtest
    change present.1 = _ at Htest
    rw [Gtest, Htest]
    have tailResult : tail.1 = serves G.toFinset H.toFinset ds := tailEq
    rw [tailResult]
    by_cases orig : d.1 ∈ reaches G.toFinset d.2
    · by_cases retained : d.1 ∈ reaches H.toFinset d.2
      · simpa only [orig, retained, decide_true, ↓reduceIte, serves, List.all_cons,
          Bool.not_true, Bool.false_or, Bool.true_and, true_and, List.length_cons] using cost
      · simpa only [orig, retained, decide_true, decide_false, ↓reduceIte, Bool.false_eq_true,
          serves, List.all_cons, Bool.not_true, Bool.false_or, Bool.false_and, true_and,
          List.length_cons] using atMostPair
    · simpa only [orig, decide_false, ↓reduceIte, Bool.false_eq_true, serves, List.all_cons,
        Bool.not_false, Bool.true_or, Bool.true_and, true_and, List.length_cons] using atMostOne

private def pruneListWithChecks (G D : List (V × V)) :
    List (V × V) → List (V × V) → List (V × V) × ℕ
  | H, [] => (H,0)
  | H, e::es =>
    let erased := H.filter (fun a => decide (e ≠ a))
    let test := servesListWithChecks G erased D
    let tail := pruneListWithChecks G D (if test.1 then erased else H) es
    (tail.1,H.length+test.2+tail.2)

def pruneStepListBudget (n m p : ℕ) : ℕ := m+p*servesListBudget n m

private theorem pruneListWithChecks_spec (G D H edges : List (V × V))
    (simple : H.Nodup) (size : H.length ≤ G.length) :
    let out := pruneListWithChecks G D H edges
    out.1.Nodup ∧ out.1.toFinset = prune G.toFinset D H.toFinset edges ∧
      out.2 ≤ edges.length*pruneStepListBudget (Fintype.card V) G.length D.length := by
  induction edges generalizing H with
  | nil => simp [pruneListWithChecks, prune, simple]
  | cons e es ih =>
    let erased := H.filter (fun a => decide (e ≠ a))
    have erasedLength : erased.length ≤ H.length := List.length_filter_le _ _
    have erasedSet : erased.toFinset = H.toFinset.erase e := by
      ext a
      simp only [erased, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, mem_erase]
      exact ⟨fun ⟨inside,different⟩ => ⟨Ne.symm different,inside⟩,
        fun ⟨different,inside⟩ => ⟨inside,Ne.symm different⟩⟩
    let test := servesListWithChecks G erased D
    obtain ⟨valid,charged⟩ := servesListWithChecks_spec G erased D (erasedLength.trans size)
    have rule : test.1 = serves G.toFinset (H.toFinset.erase e) D := by
      rw [← erasedSet]
      exact valid
    let next := if test.1 then erased else H
    have nextSimple : next.Nodup := by
      unfold next
      split
      · exact simple.filter _
      · exact simple
    have nextSize : next.length ≤ G.length := by
      unfold next
      split
      · exact erasedLength.trans size
      · exact size
    have same : next.toFinset = removeIfSafe G.toFinset D H.toFinset e := by
      unfold next removeIfSafe
      rw [rule]
      split <;> simp only [erasedSet]
    obtain ⟨nodup,outEq,outCost⟩ := ih next nextSimple nextSize
    refine ⟨nodup,?_,?_⟩
    · change (pruneListWithChecks G D next es).1.toFinset = _
      rw [outEq, same]
      rfl
    · change H.length+test.2+(pruneListWithChecks G D next es).2 ≤ _
      have each := Nat.add_le_add size charged
      exact (Nat.add_le_add each outCost).trans_eq (by
        rw [List.length_cons, Nat.succ_mul]
        unfold pruneStepListBudget
        ac_rfl)

/-- Greedy deletion on lists, using the same lexicographic edge order and reachability tests. -/
def offlinePruneListWithChecks (arcs demands : List (V × V)) : List (V × V) × ℕ :=
  let sorted := listSortWithChecks (fun a b : Lex (V × V) => decide (a ≤ b)) (arcs.map toLex)
  let result := pruneListWithChecks arcs demands arcs (sorted.1.map ofLex)
  (result.1,sorted.2+result.2)

theorem offlinePruneListWithChecks_spec (arcs demands : List (V × V)) (simple : arcs.Nodup) :
    let n := Fintype.card V
    let m := arcs.length
    let p := demands.length
    let out := offlinePruneListWithChecks arcs demands
    out.1.Nodup ∧ out.1.toFinset = offlinePrune arcs.toFinset demands ∧
      out.2 ≤ m*m.size+m*pruneStepListBudget n m p := by
  let values := arcs.toFinset.image toLex
  let listed := arcs.map (toLex : V × V → Lex (V × V))
  have listingSet : listed.toFinset = values := by ext a; simp [listed, values]
  have listingSimple : listed.Nodup := simple.map toLex.injective
  have multi : (listed : Multiset (Lex (V × V))) = values.val := by
    rw [← listingSet, ← List.toFinset_eq listingSimple]
  obtain ⟨ordered,sortCost⟩ := listSortWithChecks_finset values listed multi
  let sorted := listSortWithChecks (fun a b : Lex (V × V) => decide (a ≤ b)) listed
  let edges := sorted.1.map ofLex
  obtain ⟨resultSimple,resultEq,resultCost⟩ := pruneListWithChecks_spec arcs demands arcs edges simple le_rfl
  have orderedEq : sorted.1 = values.sort := ordered
  have edgeCount : edges.length = values.card := by
    dsimp only [edges]
    rw [List.length_map, orderedEq, length_sort]
  have total : values.card = arcs.length := by
    rw [← listingSet, List.toFinset_card_of_nodup listingSimple]
    exact List.length_map _
  refine ⟨resultSimple,?_,?_⟩
  · change (pruneListWithChecks arcs demands arcs edges).1.toFinset = _
    rw [resultEq]
    dsimp only [edges]
    rw [orderedEq]
    rfl
  · rw [edgeCount,total] at resultCost
    rw [total] at sortCost
    exact Nat.add_le_add sortCost resultCost

end OnlineReachabilityPreservers
