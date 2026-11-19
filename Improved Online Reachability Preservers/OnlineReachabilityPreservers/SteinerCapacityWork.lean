import OnlineReachabilityPreservers.SeparatorWork

/-! Materialize the weighted capacities once per separator call. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V : Type*} [LinearOrder V] [Fintype V]

private def orderedPairKeys : List (V × V) :=
  ((univ : Finset (V ×ₗ V)).sort).map ofLex

private theorem mem_orderedPairKeys (e : V × V) : e ∈ orderedPairKeys (V := V) := by
  unfold orderedPairKeys
  exact List.mem_map.mpr ⟨toLex e, by simp, rfl⟩

private theorem orderedPairKeys_length : (orderedPairKeys (V := V)).length = Fintype.card V^2 := by
  simp [orderedPairKeys, Fintype.card_prod, pow_two]

private theorem orderedPairKeys_nodup : (orderedPairKeys (V := V)).Nodup :=
  (sort_nodup (s := (univ : Finset (V ×ₗ V))) (· ≤ ·)).map
    (fun _ _ same => congrArg toLex same)

private abbrev CapacityRows (V : Type*) :=
  {rows : List ((V × V) × ℤ) // (rows.map Prod.fst).Nodup}

private def capacityWithWeightRead (edges : Arcs V) (d : WeightedNetworkDemand V)
    (weight : V × V → ℕ × ℕ) (charges : V × V → ℕ) (scale : ℕ) (e : V × V) : ℤ × ℕ :=
  if e ∈ d.free then (scale,0)
  else if e ∈ edges then
    let read := weight e
    (roundedWeightedCapacity read.1 (charges e),read.2)
  else (0,0)

private def prepareWeightedCapacityRows (edges : Arcs V) (d : WeightedNetworkDemand V)
    (weight : V × V → ℕ × ℕ) (charges : V × V → ℕ) (scale : ℕ) :
    CapacityRows V × ℕ :=
  let entries := orderedPairKeys.map fun e => (e, capacityWithWeightRead edges d weight charges scale e)
  let rows := entries.map fun row => (row.1,row.2.1)
  have nodup : (rows.map Prod.fst).Nodup := by
    simpa only [rows, entries, List.map_map, Function.comp_def, List.map_id'] using
      (orderedPairKeys_nodup (V := V))
  (⟨rows,nodup⟩, entries.length + (entries.map fun row => row.2.2).sum)

/-- One visit per ordered pair and at most `B` weight comparisons per priced arc. -/
def capacityTableWorkBound (n m B : ℕ) : ℕ := n^2 + m*B

private theorem prepareWeightedCapacityRows_spec (edges : Arcs V) (d : WeightedNetworkDemand V)
    (weight : V × V → ℕ × ℕ) (charges : V × V → ℕ) (scale B : ℕ)
    (each : ∀ e, (weight e).2 ≤ B) :
    let rows := prepareWeightedCapacityRows edges d weight charges scale
    let capacity := weightedNetworkCapacity edges d (fun e => (weight e).1) charges scale
    rows.1.val = orderedPairKeys.map (fun e => (e,capacity e)) ∧
      rows.2 ≤ capacityTableWorkBound (Fintype.card V) edges.card B := by
  let read := capacityWithWeightRead edges d weight charges scale
  have same (e : V × V) : (read e).1 = weightedNetworkCapacity edges d (fun e => (weight e).1) charges scale e := by
    unfold read capacityWithWeightRead weightedNetworkCapacity
    split
    · rfl
    · split <;> rfl
  have cost (e : V × V) : (read e).2 ≤ B := by
    unfold read capacityWithWeightRead
    split
    · exact Nat.zero_le _
    · split
      · exact each e
      · exact Nat.zero_le _
  have costZero (e : V × V) (out : e ∉ edges) : (read e).2 = 0 := by
    unfold read capacityWithWeightRead
    by_cases free : e ∈ d.free
    · rw [ite_eq_left free]
    · rw [ite_eq_right free, ite_eq_right out]
  refine ⟨?_,?_⟩
  · simp only [prepareWeightedCapacityRows, List.map_map, Function.comp_def]
    exact List.map_congr_left (fun e _ => congrArg (Prod.mk e) (same e))
  · have allKeys : (orderedPairKeys (V := V)).toFinset = univ := by
      ext e
      simp [mem_orderedPairKeys]
    have sum : (orderedPairKeys.map fun e => (read e).2).sum ≤ edges.card*B := by
      rw [← List.sum_toFinset _ orderedPairKeys_nodup, allKeys,
        ← sum_subset (subset_univ edges) (fun e _ => costZero e)]
      simpa only [sum_const, nsmul_eq_mul, Nat.cast_id] using
        sum_le_sum (s := edges) (fun e _ => cost e)
    simp only [prepareWeightedCapacityRows, List.length_map, List.map_map, Function.comp_def]
    change (orderedPairKeys (V := V)).length + (orderedPairKeys.map fun e => (read e).2).sum ≤ _
    rw [orderedPairKeys_length]
    exact Nat.add_le_add_left sum _

private def residualArcsFromCapacityRows (rows : CapacityRows V) (flow : ArcFlow V) : Arcs V × ℕ :=
  let kept := rows.val.filter fun row => flow row.1 < row.2
  let keys := kept.map Prod.fst
  have sub : keys.Sublist (rows.val.map Prod.fst) := List.filter_sublist.map _
  (⟨keys,sub.nodup rows.property⟩,rows.val.length)

private theorem residualArcsFromCapacityRows_eq (rows : CapacityRows V) (capacity flow : ArcFlow V)
    (same : rows.val = orderedPairKeys.map (fun e => (e,capacity e))) :
    residualArcsFromCapacityRows rows flow =
      (residualArcs capacity flow,Fintype.card V^2) := by
  apply Prod.ext
  · ext e
    simp [residualArcsFromCapacityRows, residualArcs, same, List.mem_map, mem_orderedPairKeys]
    exact ⟨by rintro ⟨_,_,rfl,h⟩; exact h, fun h => ⟨e.1,e.2,rfl,h⟩⟩
  · simp [residualArcsFromCapacityRows, same, orderedPairKeys_length]

/-- Build the full capacity table once. Residual graph searches reuse its
values by a linear scan of the rows, with no searches by capacity key. -/
def weightedNetworkViolationWithCapacityWork (edges : Arcs V) (d : WeightedNetworkDemand V)
    (weight : V × V → ℕ × ℕ) (scale : ℕ) (charges : V × V → ℕ) : Option (Arcs V) × ℕ :=
  let table := prepareWeightedCapacityRows edges d weight charges scale
  let out := findLowCapacityCutWithResidualWork (residualArcsFromCapacityRows table.1) d.source d.sink scale
  (out.1.map (outgoingCut edges),out.2+edges.card+table.2)

theorem weightedNetworkViolationWithCapacityWork_spec (edges : Arcs V) (d : WeightedNetworkDemand V)
    (weight : V × V → ℕ × ℕ) (scale B : ℕ) (charges : V × V → ℕ)
    (each : ∀ e, (weight e).2 ≤ B) :
    let out := weightedNetworkViolationWithCapacityWork edges d weight scale charges
    let old := weightedNetworkViolationWithSearchWork edges d (fun e => (weight e).1) scale charges
    out.1 = old.1 ∧ out.2 ≤ old.2 + capacityTableWorkBound (Fintype.card V) edges.card B := by
  obtain ⟨rows,work⟩ := prepareWeightedCapacityRows_spec edges d weight charges scale B each
  unfold weightedNetworkViolationWithCapacityWork weightedNetworkViolationWithSearchWork
  dsimp only
  have same := findLowCapacityCutWithResidualWork_eq
    (residualArcsFromCapacityRows (prepareWeightedCapacityRows edges d weight charges scale).1)
    (weightedNetworkCapacity edges d (fun e => (weight e).1) charges scale) d.source d.sink scale
    (fun f => residualArcsFromCapacityRows_eq _ _ f rows)
  rw [same]
  exact ⟨rfl,Nat.add_le_add_left work _⟩

private theorem weightedCoverLoop_compare {E : Type*} [DecidableEq E]
    (old new : (E → ℕ) → Option (Finset E) × ℕ) (fuel extra : ℕ)
    (same : ∀ state, (new state).1 = (old state).1 ∧ (new state).2 ≤ (old state).2+extra)
    (charges : E → ℕ) :
    let a := weightedCoverLoopWithSearchWork old fuel charges
    let b := weightedCoverLoopWithSearchWork new fuel charges
    b.1 = a.1 ∧ b.2 ≤ a.2+fuel*extra := by
  induction fuel generalizing charges with
  | zero => simp [weightedCoverLoopWithSearchWork]
  | succ fuel ih =>
    obtain ⟨equal,work⟩ := same charges
    cases answer : (old charges).1 with
    | none =>
      simp only [weightedCoverLoopWithSearchWork,equal,answer,true_and]
      exact work.trans (Nat.add_le_add_left (by rw [Nat.succ_mul]; omega) _)
    | some cut =>
      obtain ⟨restEq,restWork⟩ := ih (chargeWeightedCut cut charges)
      simp only [weightedCoverLoopWithSearchWork,equal,answer,restEq,true_and]
      rw [Nat.succ_mul]
      omega

/-- Run the weighted network on fixed inputs with one cached capacity
row per ordered pair in each separator call. -/
def weightedNetworkRunAtScaleWithCapacityWork (edges : Arcs V) (weight : V × V → ℕ × ℕ) (scale fuel : ℕ) :
    List (WeightedNetworkDemand V) → (V × V → ℕ) → ((V × V → ℕ) × List (Arcs V)) × ℕ
  | [], initial => ((initial,[]),0)
  | d::D, initial =>
    let first := weightedCoverLoopWithSearchWork
      (weightedNetworkViolationWithCapacityWork edges d weight scale) fuel initial
    let rest := weightedNetworkRunAtScaleWithCapacityWork edges weight scale fuel D first.1.1
    ((rest.1.1,first.1.2++rest.1.2),first.2+rest.2)

theorem weightedNetworkRunAtScaleWithCapacityWork_spec (edges : Arcs V) (weight : V × V → ℕ × ℕ)
    (scale fuel B : ℕ) (each : ∀ e, (weight e).2 ≤ B) (D : List (WeightedNetworkDemand V))
    (charges : V × V → ℕ) :
    let out := weightedNetworkRunAtScaleWithCapacityWork edges weight scale fuel D charges
    let old := weightedNetworkRunAtScaleWithSearchWork edges (fun e => (weight e).1) scale fuel D charges
    out.1 = old.1 ∧ out.2 ≤ old.2+D.length*(fuel*(capacityTableWorkBound (Fintype.card V) edges.card B)) := by
  let val := fun e => (weight e).1
  let budget := capacityTableWorkBound (Fintype.card V) edges.card B
  induction D generalizing charges with
  | nil => simp [weightedNetworkRunAtScaleWithCapacityWork,weightedNetworkRunAtScaleWithSearchWork]
  | cons d D ih =>
    let oldCheck := weightedNetworkViolationWithSearchWork edges d val scale
    let newCheck := weightedNetworkViolationWithCapacityWork edges d weight scale
    let oldFirst := weightedCoverLoopWithSearchWork oldCheck fuel charges
    let newFirst := weightedCoverLoopWithSearchWork newCheck fuel charges
    obtain ⟨firstEq,firstBound⟩ := weightedCoverLoop_compare oldCheck newCheck fuel budget
      (fun s => weightedNetworkViolationWithCapacityWork_spec edges d weight scale B s each) charges
    change newFirst.1 = oldFirst.1 at firstEq
    change newFirst.2 ≤ oldFirst.2+fuel*budget at firstBound
    obtain ⟨tailEq,tailBound⟩ := ih oldFirst.1.1
    let oldLast := weightedNetworkRunAtScaleWithSearchWork edges val scale fuel D oldFirst.1.1
    let newLast := weightedNetworkRunAtScaleWithCapacityWork edges weight scale fuel D oldFirst.1.1
    change newLast.1 = oldLast.1 at tailEq
    change newLast.2 ≤ oldLast.2+D.length*(fuel*budget) at tailBound
    change ((weightedNetworkRunAtScaleWithCapacityWork edges weight scale fuel D newFirst.1.1).1.1,
        newFirst.1.2++(weightedNetworkRunAtScaleWithCapacityWork edges weight scale fuel D newFirst.1.1).1.2) =
      (oldLast.1.1,oldFirst.1.2++oldLast.1.2) ∧
      newFirst.2+(weightedNetworkRunAtScaleWithCapacityWork edges weight scale fuel D newFirst.1.1).2 ≤
        oldFirst.2+oldLast.2+(D.length+1)*(fuel*budget)
    rw [firstEq]
    change (newLast.1.1,oldFirst.1.2++newLast.1.2) = (oldLast.1.1,oldFirst.1.2++oldLast.1.2) ∧ _
    refine ⟨by rw [tailEq],?_⟩
    change newFirst.2+newLast.2 ≤ oldFirst.2+oldLast.2+(D.length+1)*(fuel*budget)
    rw [Nat.add_mul]
    omega

end OnlineReachabilityPreservers
