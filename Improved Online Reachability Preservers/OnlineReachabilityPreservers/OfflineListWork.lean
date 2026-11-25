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

omit [Fintype V] in
private def servesListWithWork (query : List (V × V) → (V × V) → Bool × ℕ)
    (emptyCharge stepCharge : ℕ) (G H : List (V × V)) : List (V × V) → Bool × ℕ
  | [] => (true,emptyCharge)
  | d::ds =>
    let needed := query G d
    if needed.1 then
      let present := query H d
      if present.1 then
        let tail := servesListWithWork query emptyCharge stepCharge G H ds
        (tail.1,stepCharge+needed.2+present.2+tail.2)
      else (false,stepCharge+needed.2+present.2)
    else
      let tail := servesListWithWork query emptyCharge stepCharge G H ds
      (tail.1,stepCharge+needed.2+tail.2)

private theorem servesListWithWork_spec (G H D : List (V × V)) (small : H.length ≤ G.length)
    (query : List (V × V) → (V × V) → Bool × ℕ) (emptyCharge stepCharge testBound : ℕ)
    (querySpec : ∀ K d, K.length ≤ G.length → (query K d).1 = decide (d.1 ∈ reaches K.toFinset d.2) ∧
      (query K d).2 ≤ testBound) :
    let out := servesListWithWork query emptyCharge stepCharge G H D
    out.1 = serves G.toFinset H.toFinset D ∧
      out.2 ≤ emptyCharge+D.length*(stepCharge+2*testBound) := by
  induction D with
  | nil => simp [servesListWithWork,serves]
  | cons d ds ih =>
    let needed := query G d
    let present := query H d
    let tail := servesListWithWork query emptyCharge stepCharge G H ds
    obtain ⟨Gtest,Gwork⟩ := querySpec G d le_rfl
    obtain ⟨Htest,Hwork⟩ := querySpec H d small
    change needed.2 ≤ testBound at Gwork
    change present.2 ≤ testBound at Hwork
    obtain ⟨tailEq,tailCost⟩ := ih
    change tail.2 ≤ emptyCharge+ds.length*(stepCharge+2*testBound) at tailCost
    have maximum : stepCharge+needed.2+present.2+tail.2 ≤ emptyCharge+(ds.length+1)*(stepCharge+2*testBound) := by
      rw [Nat.succ_mul]
      omega
    have enoughPair := (Nat.le_add_right (stepCharge+needed.2+present.2) tail.2).trans maximum
    have enoughSingle := (Nat.add_le_add_right (Nat.le_add_right (stepCharge+needed.2) present.2) tail.2).trans maximum
    change (if needed.1 then (if present.1 then (tail.1,stepCharge+needed.2+present.2+tail.2)
      else (false,stepCharge+needed.2+present.2)) else (tail.1,stepCharge+needed.2+tail.2)).1 = _ ∧
      (if needed.1 then (if present.1 then (tail.1,stepCharge+needed.2+present.2+tail.2)
        else (false,stepCharge+needed.2+present.2)) else (tail.1,stepCharge+needed.2+tail.2)).2 ≤ _
    change needed.1 = decide (d.1 ∈ reaches G.toFinset d.2) at Gtest
    change present.1 = decide (d.1 ∈ reaches H.toFinset d.2) at Htest
    change tail.1 = serves G.toFinset H.toFinset ds at tailEq
    rw [Gtest,Htest,tailEq]
    by_cases orig : d.1 ∈ reaches G.toFinset d.2
    · by_cases retained : d.1 ∈ reaches H.toFinset d.2
      · simpa only [orig,retained,decide_true,↓reduceIte,serves,List.all_cons,
          Bool.not_true,Bool.false_or,Bool.true_and,true_and,List.length_cons] using maximum
      · simpa only [orig,retained,decide_true,decide_false,↓reduceIte,Bool.false_eq_true,
          serves,List.all_cons,Bool.not_true,Bool.false_or,Bool.false_and,true_and,List.length_cons] using enoughPair
    · simpa only [orig,decide_false,↓reduceIte,Bool.false_eq_true,serves,List.all_cons,
        Bool.not_false,Bool.true_or,Bool.true_and,true_and,List.length_cons] using enoughSingle

private def servesListWithChecks (G H : List (V × V)) : List (V × V) → Bool × ℕ :=
  servesListWithWork reachListWithChecks 0 0 G H

def servesListBudget (n m : ℕ) : ℕ := 2*(n*(m*(2*n))+n)

private theorem servesListWithChecks_spec (G H D : List (V × V)) (small : H.length ≤ G.length) :
    let out := servesListWithChecks G H D
    out.1 = serves G.toFinset H.toFinset D ∧
      out.2 ≤ D.length*servesListBudget (Fintype.card V) G.length := by
  let n := Fintype.card V
  have measured := servesListWithWork_spec G H D small reachListWithChecks 0 0 (n*(G.length*(2*n))+n) (by
    intro K d size
    obtain ⟨same, cost⟩ := reachListWithChecks_spec K d
    exact ⟨same, cost.trans (by gcongr)⟩)
  simpa only [servesListWithChecks, servesListBudget, Nat.zero_add] using measured

omit [Fintype V] in
private def pruneListWithWork (test : List (V × V) → Bool × ℕ) (emptyCharge : ℕ) (filterCharge : ℕ → ℕ) :
    List (V × V) → List (V × V) → List (V × V) × ℕ
  | H, [] => (H,emptyCharge)
  | H, e::es =>
    let erased := H.filter (fun a => decide (e ≠ a))
    let checked := test erased
    let tail := pruneListWithWork test emptyCharge filterCharge (if checked.1 then erased else H) es
    (tail.1,filterCharge H.length+checked.2+tail.2)

private theorem pruneListWithWork_spec (G D H edges : List (V × V))
    (simple : H.Nodup) (size : H.length ≤ G.length)
    (test : List (V × V) → Bool × ℕ) (emptyCharge : ℕ) (filterCharge : ℕ → ℕ) (filterBound testBound : ℕ)
    (filterCost : ∀ l ≤ G.length, filterCharge l ≤ filterBound)
    (testSpec : ∀ K, K.length ≤ G.length →
      (test K).1 = serves G.toFinset K.toFinset D ∧ (test K).2 ≤ testBound) :
    let out := pruneListWithWork test emptyCharge filterCharge H edges
    out.1.Nodup ∧ out.1.toFinset = prune G.toFinset D H.toFinset edges ∧
      out.2 ≤ emptyCharge+edges.length*(filterBound+testBound) := by
  induction edges generalizing H with
  | nil => simp [pruneListWithWork, prune, simple]
  | cons e es ih =>
    let erased := H.filter (fun a => decide (e ≠ a))
    have erasedLength : erased.length ≤ H.length := List.length_filter_le _ _
    have erasedSet : erased.toFinset = H.toFinset.erase e := by
      ext a
      simp only [erased, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, mem_erase]
      exact ⟨fun ⟨inside,different⟩ => ⟨Ne.symm different,inside⟩,
        fun ⟨different,inside⟩ => ⟨inside,Ne.symm different⟩⟩
    let tested := test erased
    obtain ⟨valid,charged⟩ := testSpec erased (erasedLength.trans size)
    have rule : tested.1 = serves G.toFinset (H.toFinset.erase e) D := by
      rw [← erasedSet]
      exact valid
    let next := if tested.1 then erased else H
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
    · change (pruneListWithWork test emptyCharge filterCharge next es).1.toFinset = _
      rw [outEq, same]
      rfl
    · change filterCharge H.length + tested.2 + (pruneListWithWork test emptyCharge filterCharge next es).2 ≤ _
      change tested.2 ≤ testBound at charged
      have thisStep := Nat.add_le_add (filterCost H.length size) charged
      change (pruneListWithWork test emptyCharge filterCharge next es).2 ≤ _ at outCost
      rw [List.length_cons, Nat.succ_mul]
      omega

private def pruneListWithChecks (G D : List (V × V)) : List (V × V) → List (V × V) → List (V × V) × ℕ :=
  pruneListWithWork (fun K => servesListWithChecks G K D) 0 id

def pruneStepListBudget (n m p : ℕ) : ℕ := m+p*servesListBudget n m

private theorem pruneListWithChecks_spec (G D H edges : List (V × V))
    (simple : H.Nodup) (size : H.length ≤ G.length) :
    let out := pruneListWithChecks G D H edges
    out.1.Nodup ∧ out.1.toFinset = prune G.toFinset D H.toFinset edges ∧
      out.2 ≤ edges.length*pruneStepListBudget (Fintype.card V) G.length D.length := by
  have measured := pruneListWithWork_spec G D H edges simple size (fun K => servesListWithChecks G K D)
    0 id G.length (D.length*servesListBudget (Fintype.card V) G.length)
    (fun _ bound => bound) (fun K size => servesListWithChecks_spec G K D size)
  simpa only [pruneListWithChecks, pruneStepListBudget, Nat.zero_add] using measured

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

section InsertionSort

variable {A : Type*} [LinearOrder A]

private def orderedInsertWithWordWork (key : A) : List A → List A × ℕ
  | [] => ([key],4)
  | first :: rest =>
    if key ≤ first then (key::first::rest,7)
    else
      let tail := orderedInsertWithWordWork key rest
      (first::tail.1,8+tail.2)

private theorem orderedInsertWithWordWork_spec (key : A) (items : List A) :
    let out := orderedInsertWithWordWork key items
    out.1 = List.orderedInsert (· ≤ ·) key items ∧ out.2 ≤ 4+8*items.length := by
  induction items with
  | nil => simp [orderedInsertWithWordWork]
  | cons a t ih =>
    by_cases first : key ≤ a
    · simp [orderedInsertWithWordWork,List.orderedInsert_cons_of_le (· ≤ ·) t first,first]
      omega
    · obtain ⟨same, work⟩ := ih
      simp only [orderedInsertWithWordWork,first,↓reduceIte,List.orderedInsert_of_not_le (· ≤ ·) t first,same,
        true_and,List.length_cons]
      omega

/-- A sorted list with a polynomial source-level tally for comparison,
traversal and list construction. Counter maintenance is excluded. -/
def insertionSortWithWordWork : List A → List A × ℕ
  | [] => ([],1)
  | a::items =>
    let tail := insertionSortWithWordWork items
    let insert := orderedInsertWithWordWork a tail.1
    (insert.1, tail.2+insert.2+5)

theorem insertionSortWithWordWork_spec (items : List A) :
    let out := insertionSortWithWordWork items
    out.1 = List.insertionSort (· ≤ ·) items ∧ out.2 ≤ 10*(items.length+1)^2 := by
  induction items with
  | nil => simp [insertionSortWithWordWork,List.insertionSort_nil]
  | cons key rest ih =>
    let tail := insertionSortWithWordWork rest
    obtain ⟨same, work⟩ := ih
    have length : tail.1.length = rest.length := by
      rw [show tail.1 = _ from same]
      exact (List.perm_insertionSort (· ≤ ·) rest).length_eq
    obtain ⟨out, bounds⟩ := orderedInsertWithWordWork_spec key tail.1
    refine ⟨?_, ?_⟩
    · change (orderedInsertWithWordWork key tail.1).1 = _
      rw [out,show tail.1 = _ from same, List.insertionSort_cons]
    · change tail.2+(orderedInsertWithWordWork key tail.1).2+5 ≤ _
      rw [length] at bounds
      change tail.2 ≤ _ at work
      simp only [List.length_cons]
      nlinarith

end InsertionSort

omit [Fintype V] in
private def servesListWithWordWork (G H : List (V × V)) (depth : ℕ) : List (V × V) → Bool × ℕ :=
  servesListWithWork (fun K d => reachTestListWithWordWork K d.1 d.2 depth) 1 7 G H

private def serveStepWordBudget (n m : ℕ) : ℕ := 7+2*(reachInListWordBudget n m+2*n+5)

private theorem servesListWithWordWork_spec (G H D : List (V × V)) (small : H.length ≤ G.length) :
    let n := Fintype.card V
    let out := servesListWithWordWork G H n D
    out.1 = serves G.toFinset H.toFinset D ∧
      out.2 ≤ 1+D.length*serveStepWordBudget n G.length := by
  let n := Fintype.card V
  exact servesListWithWork_spec G H D small (fun K d => reachTestListWithWordWork K d.1 d.2 n) 1 7
    (reachInListWordBudget n G.length+2*n+5) (by
      intro K d size
      obtain ⟨same, cost⟩ := reachTestListWithWordWork_spec K d.1 d.2 n
      exact ⟨same, cost.trans (by unfold reachInListWordBudget; gcongr)⟩)

omit [Fintype V] in
private def pruneListWithWordWork (G D : List (V × V)) (depth : ℕ) :
    List (V × V) → List (V × V) → List (V × V) × ℕ :=
  pruneListWithWork (fun K => servesListWithWordWork G K depth D) 1 (fun l => 9*l+8)

private def pruneStepWordBudget (n m p : ℕ) : ℕ := 9*m+1+p*serveStepWordBudget n m+8

private theorem pruneListWithWordWork_spec (G D H edges : List (V × V))
    (simple : H.Nodup) (size : H.length ≤ G.length) :
    let n := Fintype.card V
    let out := pruneListWithWordWork G D n H edges
    out.1.Nodup ∧ out.1.toFinset = prune G.toFinset D H.toFinset edges ∧
      out.2 ≤ 1+edges.length*pruneStepWordBudget n G.length D.length := by
  let n := Fintype.card V
  have measured := pruneListWithWork_spec G D H edges simple size (fun K => servesListWithWordWork G K n D)
    1 (fun l => 9*l+8) (9*G.length+8) (1+D.length*serveStepWordBudget n G.length)
    (fun _ bound => by gcongr) (fun K size => servesListWithWordWork_spec G K D size)
  have perEdge : 9*G.length+8+(1+D.length*serveStepWordBudget n G.length) =
      pruneStepWordBudget n G.length D.length := by unfold pruneStepWordBudget; ring
  simpa only [pruneListWithWordWork,perEdge] using measured

/-- Sort the raw edges into the canonical order, then perform the exact
reachability-preserving greedy deletion. -/
def offlinePruneListWithWordWork (arcs : List (V × V)) (depth : ℕ) (demands : List (V × V)) : List (V × V) × ℕ :=
  let sorted := insertionSortWithWordWork (arcs.map toLex)
  let out := pruneListWithWordWork arcs demands depth arcs (sorted.1.map ofLex)
  (out.1,sorted.2+out.2+12*arcs.length+5)

def offlinePruningWordBudget (n m p : ℕ) : ℕ := 10*(m+1)^2+1+m*pruneStepWordBudget n m p+12*m+5

theorem offlinePruneListWithWordWork_spec (arcs demands : List (V × V)) (simple : arcs.Nodup) :
    let n := Fintype.card V
    let m := arcs.length
    let p := demands.length
    let out := offlinePruneListWithWordWork arcs n demands
    out.1.Nodup ∧ out.1.toFinset = offlinePrune arcs.toFinset demands ∧
      out.2 ≤ offlinePruningWordBudget n m p := by
  let values := arcs.toFinset.image toLex
  let listed := arcs.map (toLex : V × V → Lex (V × V))
  let sorted := insertionSortWithWordWork listed
  let edges := sorted.1.map ofLex
  have listingSet : listed.toFinset = values := by ext a; simp [listed,values]
  have listingSimple : listed.Nodup := simple.map toLex.injective
  have multi : (listed : Multiset (Lex (V × V))) = values.val := by
    rw [← listingSet, ← List.toFinset_eq listingSimple]
  obtain ⟨ordered, sortCost⟩ := insertionSortWithWordWork_spec listed
  obtain ⟨clean,resultEq,resultCost⟩ := pruneListWithWordWork_spec arcs demands arcs edges simple le_rfl
  have orderedEq : sorted.1 = values.sort := by
    change sorted.1 = _ at ordered
    rw [ordered, ← List.mergeSort_eq_insertionSort]
    exact (listSortWithChecks_spec (fun a b => decide (a ≤ b)) listed).1.symm.trans
      (listSortWithChecks_finset values listed multi).1
  have total : values.card = arcs.length := by
    rw [← listingSet, List.toFinset_card_of_nodup listingSimple]
    exact List.length_map _
  have edgeCount : edges.length = arcs.length := by
    dsimp only [edges]
    rw [List.length_map, orderedEq, length_sort, total]
  refine ⟨clean,?_,?_⟩
  · change (pruneListWithWordWork arcs demands (Fintype.card V) arcs edges).1.toFinset = _
    rw [resultEq]
    dsimp only [edges]
    rw [orderedEq]
    rfl
  · change sorted.2+(pruneListWithWordWork arcs demands (Fintype.card V) arcs edges).2+12*arcs.length+5 ≤ _
    have sortCap : sorted.2 ≤ 10*(arcs.length+1)^2 := by simpa only [listed,List.length_map] using sortCost
    rw [edgeCount] at resultCost
    exact (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add sortCap resultCost) _) _).trans_eq
      (by unfold offlinePruningWordBudget; ring)

theorem offlinePruningWordBudget_mono_arcs (n p : ℕ) : Monotone fun m => offlinePruningWordBudget n m p := by
  intro m k small
  dsimp only [offlinePruningWordBudget,pruneStepWordBudget,serveStepWordBudget,reachInListWordBudget]
  gcongr

end OnlineReachabilityPreservers
