import OnlineReachabilityPreservers.DeterministicListWork

/-! Cache the labels used by the SCC reduction and count the key operations in
building and applying that cache. -/

namespace OnlineReachabilityPreservers

open Finset

def mapListWithChecks {A B : Type*} (f : A → B × ℕ) : List A → List B × ℕ
  | [] => ([], 0)
  | x::xs =>
    let first := f x
    let tail := mapListWithChecks f xs
    (first.1 :: tail.1, first.2 + tail.2)

theorem mapListWithChecks_spec {A B : Type*} (f : A → B × ℕ) (value : A → B)
    (xs : List A) (budget : ℕ) (same : ∀ x ∈ xs, (f x).1 = value x)
    (cost : ∀ x ∈ xs, (f x).2 ≤ budget) :
    let out := mapListWithChecks f xs
    out.1 = xs.map value ∧ out.2 ≤ xs.length * budget := by
  induction xs with
  | nil => simp [mapListWithChecks]
  | cons x xs ih =>
    obtain ⟨tail, work⟩ := ih (fun a ha => same a (List.mem_cons_of_mem _ ha))
      (fun a ha => cost a (List.mem_cons_of_mem _ ha))
    refine ⟨?_, ?_⟩
    · simp only [mapListWithChecks, tail, same x List.mem_cons_self, List.map_cons]
    · exact (Nat.add_le_add (cost x List.mem_cons_self) work).trans_eq (by
        rw [List.length_cons, Nat.succ_mul, add_comm])

variable {V : Type*} [LinearOrder V] [Fintype V]

omit [Fintype V] in
theorem reverseArcList_toFinset (arcs : List (V × V)) :
    (arcs.map Prod.swap).toFinset = reverseArcs arcs.toFinset := by
  ext e
  simp [reverseArcs]

private def componentLabelListWithMeasure (countWords : Bool) (arcs transpose : List (V × V))
    (depth : ℕ) (v : V) : V × ℕ :=
  let search := if countWords then reachInListWithWordWork else reachInListWithChecks
  let inward := search arcs v depth
  let outward := search transpose v depth
  let label := leastWhereWithChecks (fun u =>
    if countWords then memScanWithWordWork u outward.1
    else anyWithChecks (fun w => decide (u = w)) outward.1) inward.1
  let work := inward.2 + outward.2 + label.2
  (label.1.getD v, if countWords then work + 10*inward.1.length + 7 else work)

private def componentLabelListWithChecks (arcs transpose : List (V × V)) (v : V) : V × ℕ :=
  componentLabelListWithMeasure false arcs transpose (Fintype.card V) v

private theorem componentLabelListWithChecks_spec (arcs : List (V × V)) (v : V) :
    let n := Fintype.card V
    let out := componentLabelListWithChecks arcs (arcs.map Prod.swap) v
    out.1 = componentLabel arcs.toFinset v ∧
      out.2 ≤ 2*(n*(arcs.length*(2*n))) + n*(n+1) := by
  let n := Fintype.card V
  let inward := reachInListWithChecks arcs v n
  let outward := reachInListWithChecks (arcs.map Prod.swap) v n
  obtain ⟨inSimple, inResult, inWork⟩ := reachInListWithChecks_spec arcs v n
  obtain ⟨outSimple, outResult, outWork⟩ := reachInListWithChecks_spec (arcs.map Prod.swap) v n
  have inSize : inward.1.length ≤ n := by
    rw [← List.toFinset_card_of_nodup inSimple]
    exact card_le_univ _
  have outSize : outward.1.length ≤ n := by
    rw [← List.toFinset_card_of_nodup outSimple]
    exact card_le_univ _
  obtain ⟨minimum, comparisons⟩ := leastWhereWithChecks_spec
    (fun u => anyWithChecks (fun w => decide (u=w)) outward.1)
    (fun u => u ∈ outward.1) inward.1 n
    (fun u _ => (memScanWithChecks_spec u outward.1).1)
    (fun u _ => (memScanWithChecks_spec u outward.1).2.trans outSize)
  refine ⟨?_, ?_⟩
  · simp only [componentLabelListWithChecks, componentLabelListWithMeasure, Bool.false_eq_true,
      ↓reduceIte, componentLabel, componentVertices, reaches]
    change (leastWhereWithChecks _ inward.1).1.getD v = _
    rw [minimum]
    have sets : inward.1.toFinset.filter (fun u => u ∈ outward.1) =
        reachIn arcs.toFinset v n ∩ reachIn (reverseArcs arcs.toFinset) v n := by
      have inEq : inward.1.toFinset = reachIn arcs.toFinset v n := inResult
      have outEq : outward.1.toFinset = reachIn (reverseArcs arcs.toFinset) v n := by
        simpa only [reverseArcList_toFinset] using outResult
      ext u
      simp only [mem_filter, mem_inter, ← inEq, ← outEq, List.mem_toFinset]
    rw [sets]
  · have labelWork := comparisons.trans (Nat.mul_le_mul_right (n+1) inSize)
    have pairWork := Nat.add_le_add inWork (by simpa only [List.length_map] using outWork)
    exact Nat.add_le_add (pairWork.trans_eq (by ring)) labelWork

/-- Prepare all SCC labels in one table. The transpose is shared by its rows. -/
def componentLabelTableWithChecks (arcs : List (V × V)) (vertices : List V) : List (V × V) × ℕ :=
  let transpose := arcs.map Prod.swap
  mapListWithChecks (fun v =>
    let label := componentLabelListWithChecks arcs transpose v
    ((v,label.1),label.2)) vertices

theorem componentLabelTableWithChecks_spec (arcs : List (V × V)) (vertices : List V) :
    let n := Fintype.card V
    let out := componentLabelTableWithChecks arcs vertices
    out.1 = vertices.map (fun v => (v,componentLabel arcs.toFinset v)) ∧
      out.2 ≤ vertices.length*(2*(n*(arcs.length*(2*n)))+n*(n+1)) := by
  apply mapListWithChecks_spec
  · intro v _
    change (v,(componentLabelListWithChecks arcs (arcs.map Prod.swap) v).1) = _
    rw [(componentLabelListWithChecks_spec arcs v).1]
  · intro v _
    exact (componentLabelListWithChecks_spec arcs v).2

omit [Fintype V] in
private def lookupLabelWithChecks (v : V) : List (V × V) → V × ℕ
  | [] => (v,0)
  | (key,label)::rows =>
    if v = key then (label,1)
    else let out := lookupLabelWithChecks v rows
         (out.1, out.2+1)

omit [Fintype V] in
private theorem lookupLabelWithChecks_spec (label : V → V) (vertices : List V) (v : V) (inside : v ∈ vertices) :
    let out := lookupLabelWithChecks v (vertices.map (fun w => (w,label w)))
    out.1 = label v ∧ out.2 ≤ vertices.length := by
  induction vertices with
  | nil => contradiction
  | cons w rest ih =>
    by_cases eq : v = w
    · subst w
      simp [lookupLabelWithChecks]
    · have tail : v ∈ rest := (List.mem_cons.mp inside).resolve_left eq
      obtain ⟨same, cost⟩ := ih tail
      simp only [List.map_cons, lookupLabelWithChecks, eq, ↓reduceIte, same, true_and, List.length_cons]
      exact Nat.succ_le_succ cost

omit [Fintype V] in
/-- Use a prepared SCC label table to project a list of pairs. -/
def projectPairsWithChecks (table : List (V × V)) (pairs : List (V × V)) : List (V × V) × ℕ :=
  mapListWithChecks (fun e =>
    let source := lookupLabelWithChecks e.1 table
    let sink := lookupLabelWithChecks e.2 table
    ((source.1,sink.1),source.2+sink.2)) pairs

omit [Fintype V] in
theorem projectPairsWithChecks_spec (label : V → V) (keys : List V) (pairs : List (V × V))
    (enumerate : ∀ v : V, v ∈ keys) :
    let table := keys.map (fun v => (v,label v))
    let out := projectPairsWithChecks table pairs
    out.1 = pairs.map (fun e => (label e.1,label e.2)) ∧ out.2 ≤ pairs.length*(2*keys.length) := by
  have entry (v : V) := lookupLabelWithChecks_spec label keys v (enumerate v)
  apply mapListWithChecks_spec
  · intro e _
    change ((lookupLabelWithChecks e.1 _).1, (lookupLabelWithChecks e.2 _).1) = _
    rw [(entry e.1).1, (entry e.2).1]
  · intro e _
    exact (Nat.add_le_add (entry e.1).2 (entry e.2).2).trans_eq (by rw [two_mul])

omit [Fintype V] in
/-- Project a list of individual vertices through the shared label table,
charging the table search and each mapped list cell. -/
def projectVerticesWithWordWork (table : List (V × V)) (items : List V) : List V × ℕ :=
  let result := mapListWithChecks (fun v => lookupLabelWithChecks v table) items
  (result.1,4*result.2+8*items.length+4)

omit [Fintype V] in
theorem projectVerticesWithWordWork_spec (label : V → V) (vertices items : List V)
    (complete : ∀ v : V, v ∈ vertices) :
    let table := vertices.map (fun v => (v,label v))
    let out := projectVerticesWithWordWork table items
    out.1 = items.map label ∧ out.2 ≤ 4*(items.length*(vertices.length+1))+8*items.length+4 := by
  let table := vertices.map (fun v => (v,label v))
  have entry (v : V) := lookupLabelWithChecks_spec label vertices v (complete v)
  obtain ⟨same, cost⟩ := mapListWithChecks_spec (fun v => lookupLabelWithChecks v table) label
    items vertices.length (fun v _ => (entry v).1) (fun v _ => (entry v).2)
  have cap := cost.trans (Nat.mul_le_mul_left items.length (Nat.le_succ vertices.length))
  exact ⟨same, Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_left 4 cap) _) _⟩

/-- Project the arc list once, remove same-component pairs, and deduplicate. -/
def condensationListWithChecks (table arcs : List (V × V)) : List (V × V) × ℕ :=
  let projected := projectPairsWithChecks table arcs
  let crossing := projected.1.filter (fun e => decide (e.1 ≠ e.2))
  let unique := insertListWithChecks crossing []
  (unique.1, projected.2 + projected.1.length + unique.2)

theorem condensationListWithChecks_spec (arcs : List (V × V)) (keys : List V)
    (enumerate : ∀ v : V, v ∈ keys) :
    let table := keys.map (fun v => (v,componentLabel arcs.toFinset v))
    let n := Fintype.card V
    let out := condensationListWithChecks table arcs
    out.1.Nodup ∧ out.1.toFinset = condensation arcs.toFinset ∧
      out.1.length ≤ arcs.length ∧ out.2 ≤ arcs.length*(2*keys.length+1+n^2) := by
  let table := keys.map (fun v => (v,componentLabel arcs.toFinset v))
  let projected := projectPairsWithChecks table arcs
  let crossing := projected.1.filter (fun e => decide (e.1 ≠ e.2))
  let unique := insertListWithChecks crossing []
  obtain ⟨result,projecting⟩ := projectPairsWithChecks_spec
    (componentLabel arcs.toFinset) keys arcs enumerate
  change projected.1 = arcs.map (projectDemand arcs.toFinset) at result
  have pairCount : projected.1.length = arcs.length := by rw [result, List.length_map]
  have crossingSize : crossing.length ≤ arcs.length := (List.length_filter_le _ _).trans_eq pairCount
  obtain ⟨simple,deduplicated,insertions⟩ := insertListWithChecks_spec crossing [] (by simp)
  have crossingSet : crossing.toFinset = condensation arcs.toFinset := by
    unfold crossing
    rw [result]
    ext key
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq, List.mem_map,
      condensation, mem_image, mem_filter]
    constructor
    · rintro ⟨⟨e,inside,rfl⟩,different⟩
      exact ⟨e,⟨inside,different⟩,rfl⟩
    · rintro ⟨e,⟨inside,different⟩,rfl⟩
      exact ⟨⟨e,inside,rfl⟩,different⟩
  have same : unique.1.toFinset = condensation arcs.toFinset := by
    simpa only [List.toFinset_nil, empty_union, crossingSet] using deduplicated
  refine ⟨simple,same,?_,?_⟩
  · change unique.1.length ≤ _
    rw [← List.toFinset_card_of_nodup simple, deduplicated]
    simp only [List.toFinset_nil, empty_union]
    exact (List.toFinset_card_le _).trans crossingSize
  · change projected.2 + projected.1.length + unique.2 ≤ _
    rw [pairCount]
    have size : unique.2 ≤ arcs.length*(Fintype.card V)^2 := by
      rw [pow_two, ← Fintype.card_prod]
      exact insertions.trans (Nat.mul_le_mul_right _ crossingSize)
    exact (Nat.add_le_add (Nat.add_le_add projecting le_rfl) size).trans_eq (by ring)

/-- The comparison budget for building the shared label table and its condensation. -/
def condensationListBudget (n m : ℕ) : ℕ :=
  n*(2*(n*(m*(2*n)))+n*(n+1)) + m*(2*n+1+n^2)

/-- Build the label table once and use it to condense the original arc list. -/
def prepareCondensationWithChecks (arcs : List (V × V)) (vertices : List V) :
    (List (V × V) × List (V × V)) × ℕ :=
  let labels := componentLabelTableWithChecks arcs vertices
  let graph := condensationListWithChecks labels.1 arcs
  ((labels.1,graph.1), labels.2+graph.2)

theorem prepareCondensationWithChecks_spec (arcs : List (V × V)) (vertices : List V)
    (simple : vertices.Nodup) (enumerate : ∀ v : V, v ∈ vertices) :
    let n := Fintype.card V
    let out := prepareCondensationWithChecks arcs vertices
    out.1.1 = vertices.map (fun v => (v,componentLabel arcs.toFinset v)) ∧
      out.1.2.Nodup ∧ out.1.2.toFinset = condensation arcs.toFinset ∧
      out.1.2.length ≤ arcs.length ∧ out.2 ≤ condensationListBudget n arcs.length := by
  have cover : vertices.toFinset = univ := by ext v; simp [enumerate v]
  have count : vertices.length = Fintype.card V := by
    rw [← List.toFinset_card_of_nodup simple, cover, card_univ]
  obtain ⟨table, prep⟩ := componentLabelTableWithChecks_spec arcs vertices
  have graph := condensationListWithChecks_spec arcs vertices enumerate
  unfold prepareCondensationWithChecks
  dsimp only
  rw [table]
  exact ⟨rfl, graph.1, graph.2.1, graph.2.2.1, by
    unfold condensationListBudget
    exact Nat.add_le_add (by simpa only [count] using prep) (by simpa only [count] using graph.2.2.2)⟩

/-- Thread the prepared labels into the demand projection and run the
ordinary forward rule on the list-backed condensation. -/
def condensedForwardListWithChecks (arcs : List (V × V)) (vertices : List V)
    (demands : List (V × V)) : List (V × V) × ℕ :=
  let prepared := prepareCondensationWithChecks arcs vertices
  let projected := projectPairsWithChecks prepared.1.1 demands
  let result := forwardRunListWithChecks prepared.1.2 projected.1 []
  (result.1, prepared.2+projected.2+result.2)

theorem condensedForwardListWithChecks_spec (arcs : List (V × V)) (vertices : List V)
    (demands : List (V × V)) (simple : vertices.Nodup) (enumerate : ∀ v : V, v ∈ vertices) :
    let n := Fintype.card V
    let out := condensedForwardListWithChecks arcs vertices demands
    out.1.Nodup ∧
      out.1.toFinset = forwardRun (condensation arcs.toFinset) (demands.map (projectDemand arcs.toFinset)) ∧
      out.2 ≤ condensationListBudget n arcs.length + demands.length*(2*n+forwardStepListBudget n arcs.length) := by
  let n := Fintype.card V
  let prepared := prepareCondensationWithChecks arcs vertices
  let projected := projectPairsWithChecks prepared.1.1 demands
  obtain ⟨labels,_,graph,edges,prep⟩ := prepareCondensationWithChecks_spec arcs vertices simple enumerate
  have labelsEq : prepared.1.1 = vertices.map (fun v => (v,componentLabel arcs.toFinset v)) := labels
  obtain ⟨requests,queryCost⟩ := projectPairsWithChecks_spec
    (componentLabel arcs.toFinset) vertices demands enumerate
  have trace : projected.1 = demands.map (projectDemand arcs.toFinset) := by
    unfold projected
    rw [labelsEq]
    exact requests
  have cover : vertices.toFinset = univ := by ext v; simp [enumerate v]
  have count : vertices.length = n := by
    rw [← List.toFinset_card_of_nodup simple, cover, card_univ]
  have queries : projected.2 ≤ demands.length*(2*n) := by
    unfold projected
    rw [labelsEq]
    simpa only [count] using queryCost
  obtain ⟨outputSimple,output,work⟩ := forwardRunListWithChecks_spec prepared.1.2 projected.1 [] (by simp)
  have step : forwardStepListBudget n prepared.1.2.length ≤ forwardStepListBudget n arcs.length := by
    unfold forwardStepListBudget
    gcongr
  refine ⟨outputSimple, ?_, ?_⟩
  · change (forwardRunListWithChecks prepared.1.2 projected.1 []).1.toFinset = _
    have graphEq : prepared.1.2.toFinset = condensation arcs.toFinset := graph
    rw [output, graphEq, trace]
    rfl
  · have runCost := work.trans (Nat.mul_le_mul_left projected.1.length step)
    have requestCount : projected.1.length = demands.length := by rw [trace, List.length_map]
    rw [requestCount] at runCost
    change prepared.2+projected.2+(forwardRunListWithChecks prepared.1.2 projected.1 []).2 ≤
      condensationListBudget n arcs.length + demands.length*(2*n+forwardStepListBudget n arcs.length)
    exact (Nat.add_le_add (Nat.add_le_add prep queries) runCost).trans_eq (by ring)

private def labelRowWordBudget (n m : ℕ) : ℕ := 2 * reachInListWordBudget n m + n * (2*n+12) + 7

private def componentLabelWithWordWork (arcs transpose : List (V × V)) (depth : ℕ) (v : V) : V × ℕ :=
  componentLabelListWithMeasure true arcs transpose depth v

private theorem componentLabelWithWordWork_spec (arcs : List (V × V)) (v : V) :
    let n := Fintype.card V
    let out := componentLabelWithWordWork arcs (arcs.map Prod.swap) n v
    out.1 = componentLabel arcs.toFinset v ∧ out.2 ≤ labelRowWordBudget n arcs.length := by
  let n := Fintype.card V
  let inward := reachInListWithWordWork arcs v n
  let outward := reachInListWithWordWork (arcs.map Prod.swap) v n
  obtain ⟨inSimple, inResult, inWork⟩ := reachInListWithWordWork_spec arcs v n
  obtain ⟨outSimple, outResult, outWork⟩ := reachInListWithWordWork_spec (arcs.map Prod.swap) v n
  have inSize : inward.1.length ≤ n := by
    rw [← List.toFinset_card_of_nodup inSimple]
    exact card_le_univ _
  have outSize : outward.1.length ≤ n := by
    rw [← List.toFinset_card_of_nodup outSimple]
    exact card_le_univ _
  obtain ⟨label, labelWork⟩ := leastWhereWithChecks_spec
    (fun u => memScanWithWordWork u outward.1) (fun u => u ∈ outward.1) inward.1 (2*n+1)
    (fun u _ => (memScanWithWordWork_spec u outward.1).1)
    (fun u _ => (memScanWithWordWork_spec u outward.1).2.trans (by omega))
  refine ⟨?_,?_⟩
  · change (leastWhereWithChecks (fun u => memScanWithWordWork u outward.1) inward.1).1.getD v = _
    rw [label]
    have sets : inward.1.toFinset.filter (fun u => u ∈ outward.1) = componentVertices arcs.toFinset v := by
      have inEq : inward.1.toFinset = reachIn arcs.toFinset v n := inResult
      have outEq : outward.1.toFinset = reachIn (reverseArcs arcs.toFinset) v n := by
        simpa only [reverseArcList_toFinset] using outResult
      change _ = reachIn arcs.toFinset v n ∩ reachIn (reverseArcs arcs.toFinset) v n
      ext u
      simp only [mem_filter, mem_inter, ← inEq, ← outEq, List.mem_toFinset]
    rw [sets]
    rfl
  · change inward.2 + outward.2 + (leastWhereWithChecks _ inward.1).2 + 10*inward.1.length+7 ≤ _
    have forwardBudget : inward.2 ≤ reachInListWordBudget n arcs.length := inWork
    have reverseBudget : outward.2 ≤ reachInListWordBudget n arcs.length := by
      simpa only [reachInListWordBudget, List.length_map] using outWork
    have choiceBudget := labelWork.trans (Nat.mul_le_mul_right (2*n+1+1) inSize)
    have sumBudget := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add forwardBudget reverseBudget) choiceBudget)
      (Nat.mul_le_mul_left 10 inSize)
    exact (Nat.add_le_add_right sumBudget 7).trans_eq (by unfold labelRowWordBudget; ring)

/-- Build the transpose and the shared label table from the supplied lists.
The reported tally includes reading the vertex count, swapping the raw arc
pairs, the reverse scans, and fixed charges for each output label row.
Counter maintenance, including length scans used only for charging, is
excluded from this source-level model. -/
def componentLabelTableWithWordWork (arcs : List (V × V)) (vertices : List V) : List (V × V) × ℕ :=
  let depth := vertices.length
  let transpose := arcs.map Prod.swap
  let table := mapListWithChecks (fun v =>
    let label := componentLabelWithWordWork arcs transpose depth v
    ((v,label.1),label.2)) vertices
  (table.1, table.2+5+6*arcs.length+8*depth)

theorem componentLabelTableWithWordWork_spec (arcs : List (V × V)) (vertices : List V)
    (simple : vertices.Nodup) (enumerate : ∀ v : V, v ∈ vertices) :
    let n := Fintype.card V
    let out := componentLabelTableWithWordWork arcs vertices
    out.1 = vertices.map (fun v => (v,componentLabel arcs.toFinset v)) ∧
      out.2 ≤ n * labelRowWordBudget n arcs.length + 5 + 6*arcs.length + 8*n := by
  have cover : vertices.toFinset = univ := by ext v; simp [enumerate v]
  have size : vertices.length = Fintype.card V := by
    rw [← List.toFinset_card_of_nodup simple, cover, card_univ]
  let row (v : V) :=
    let label := componentLabelWithWordWork arcs (arcs.map Prod.swap) (Fintype.card V) v
    ((v,label.1),label.2)
  obtain ⟨same, work⟩ := mapListWithChecks_spec row
    (fun v => (v,componentLabel arcs.toFinset v)) vertices (labelRowWordBudget (Fintype.card V) arcs.length)
    (fun v _ => congrArg (Prod.mk v) (componentLabelWithWordWork_spec arcs v).1)
    (fun v _ => (componentLabelWithWordWork_spec arcs v).2)
  unfold componentLabelTableWithWordWork
  dsimp only
  rw [size]
  exact ⟨same, Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right (by simpa only [size] using work) 5) _) _⟩

/-- Bound the source-level word tally for projection, filtering, and deduplication.
The first term covers list inspections and fixed key operations inside scans.
The linear allowance covers the outer map, filter, and insertion traversals. -/
def quotientWordBudget (n m : ℕ) : ℕ := 4*(m*(2*n+1+n^2)) + 32*m + 8

private def condensationListWithWordWork (table arcs : List (V × V)) : List (V × V) × ℕ :=
  let graph := condensationListWithChecks table arcs
  (graph.1, 4*graph.2 + 32*arcs.length + 8)

/-- Prepare exact SCC labels and the quotient graph with a shared label table. -/
def prepareCondensationWithWordWork (arcs : List (V × V)) (vertices : List V) :
    (List (V × V) × List (V × V)) × ℕ :=
  let labels := componentLabelTableWithWordWork arcs vertices
  let graph := condensationListWithWordWork labels.1 arcs
  ((labels.1, graph.1), labels.2 + graph.2 + 5)

def prepareCondensationWordBudget (n m : ℕ) : ℕ :=
  n * labelRowWordBudget n m + 5 + 6*m + 8*n + quotientWordBudget n m + 5

/-- The label table and quotient are exact, with an explicit polynomial
source-level tally in the length of the raw arc list and the vertex count. -/
theorem prepareCondensationWithWordWork_spec (arcs : List (V × V)) (vertices : List V)
    (simple : vertices.Nodup) (enumerate : ∀ v : V, v ∈ vertices) :
    let n := Fintype.card V
    let out := prepareCondensationWithWordWork arcs vertices
    out.1.1 = vertices.map (fun v => (v,componentLabel arcs.toFinset v)) ∧
      out.1.2.Nodup ∧ out.1.2.toFinset = condensation arcs.toFinset ∧
      out.1.2.length ≤ arcs.length ∧ out.2 ≤ prepareCondensationWordBudget n arcs.length := by
  let n := Fintype.card V
  let m := arcs.length
  let labels := componentLabelTableWithWordWork arcs vertices
  have cover : vertices.toFinset = univ := by ext v; simp [enumerate v]
  have size : vertices.length = n := by
    rw [← List.toFinset_card_of_nodup simple, cover, card_univ]
  obtain ⟨table, prep⟩ := componentLabelTableWithWordWork_spec arcs vertices simple enumerate
  obtain ⟨graphSimple, graph, graphSize, projected⟩ := condensationListWithChecks_spec arcs vertices enumerate
  change labels.1 = _ at table
  have chartSimple : (condensationListWithChecks labels.1 arcs).1.Nodup := by rw [table]; exact graphSimple
  have chart : (condensationListWithChecks labels.1 arcs).1.toFinset = condensation arcs.toFinset := by rw [table]; exact graph
  have chartSize : (condensationListWithChecks labels.1 arcs).1.length ≤ m := by rw [table]; exact graphSize
  have cost : (condensationListWithWordWork labels.1 arcs).2 ≤ quotientWordBudget n m := by
    unfold condensationListWithWordWork quotientWordBudget
    rw [table]
    exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_left 4 (by simpa only [size] using projected)) _) _
  exact ⟨table, chartSimple, chart, chartSize, Nat.add_le_add_right (Nat.add_le_add prep cost) 5⟩

end OnlineReachabilityPreservers
