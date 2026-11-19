import OnlineReachabilityPreservers.SeparatorWork

/-! Read each original weight once when preparing a weighted separator. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V : Type*} [LinearOrder V] [Fintype V]

private def lookupWeightedCapacity (rows : List ((V × V) × ℤ)) (e : V × V) : ℤ :=
  match rows with
  | [] => 0
  | (a,value)::more => if a = e then value else lookupWeightedCapacity more e

omit [Fintype V] in
private theorem lookupWeightedCapacity_map (L : List (V × V)) (value : V × V → ℤ) (e : V × V) :
    lookupWeightedCapacity (L.map fun a => (a,value a)) e = if e ∈ L then value e else 0 := by
  induction L with
  | nil => simp [lookupWeightedCapacity]
  | cons a L ih =>
    by_cases same : a = e
    · simp [lookupWeightedCapacity,same]
    · simp [lookupWeightedCapacity,same,Ne.symm same,ih]

private def orderedPairs (edges : Arcs V) : List (V × V) :=
  ((edges.map toLex.toEmbedding).sort).map ofLex

omit [Fintype V] in
private theorem mem_orderedPairs (edges : Arcs V) (e : V × V) : e ∈ orderedPairs edges ↔ e ∈ edges := by
  constructor
  · intro h
    obtain ⟨key, inside, rfl⟩ := List.mem_map.mp h
    obtain ⟨pair, present, rfl⟩ := mem_map.mp ((mem_sort _).mp inside)
    exact present
  · intro h
    exact List.mem_map.mpr ⟨toLex e,(mem_sort _).mpr (mem_map_of_mem _ h),rfl⟩

private def prepareWeightedCapacity (edges : Arcs V) (d : WeightedNetworkDemand V)
    (weight : V × V → ℕ × ℕ) (charges : V × V → ℕ) (scale : ℕ) : ArcFlow V × ℕ :=
  let keys := orderedPairs edges
  let evaluated := keys.map fun e =>
    let w := weight e
    (e, (roundedWeightedCapacity w.1 (charges e) : ℤ),w.2)
  let rows := evaluated.map fun e => (e.1,e.2.1)
  (fun e => if e ∈ d.free then scale else lookupWeightedCapacity rows e,
    (evaluated.map fun e => e.2.2).sum)

omit [Fintype V] in
private theorem prepareWeightedCapacity_spec (edges : Arcs V) (d : WeightedNetworkDemand V)
    (weight : V × V → ℕ × ℕ) (charges : V × V → ℕ) (scale B : ℕ)
    (each : ∀ e, (weight e).2 ≤ B) :
    let cap := prepareWeightedCapacity edges d weight charges scale
    cap.1 = weightedNetworkCapacity edges d (fun e => (weight e).1) charges scale ∧
      cap.2 ≤ edges.card*B := by
  let keys := orderedPairs edges
  let val (e : V × V) : ℤ := roundedWeightedCapacity (weight e).1 (charges e)
  have valueEq : ∀ e, lookupWeightedCapacity (keys.map fun a => (a,val a)) e =
      if e ∈ edges then val e else 0 := by
    intro e
    simpa only [keys, mem_orderedPairs] using lookupWeightedCapacity_map keys val e
  have rowBound (L : List (V × V)) : (L.map fun e => (weight e).2).sum ≤ L.length*B := by
    induction L with
    | nil => simp
    | cons e more ih =>
      simpa only [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul,Nat.add_comm] using
        Nat.add_le_add (each e) ih
  refine ⟨?_,?_⟩
  · funext e
    unfold prepareWeightedCapacity weightedNetworkCapacity
    simp only [List.map_map]
    exact congrArg (fun z : ℤ => if e ∈ d.free then (scale : ℤ) else z) (valueEq e)
  · unfold prepareWeightedCapacity
    simp only [List.map_map]
    exact (rowBound keys).trans_eq (by simp [keys, orderedPairs])

/-- Each separator computes its priced capacities once and shares the
result throughout augmentation and the final residual reachability test. -/
def weightedNetworkViolationWithCapacityWork (edges : Arcs V) (d : WeightedNetworkDemand V)
    (weight : V × V → ℕ × ℕ) (scale : ℕ) (charges : V × V → ℕ) : Option (Arcs V) × ℕ :=
  let cap := prepareWeightedCapacity edges d weight charges scale
  let out := findLowCapacityCutWithSearchWork cap.1 d.source d.sink scale
  (out.1.map (outgoingCut edges),out.2+edges.card+cap.2)

theorem weightedNetworkViolationWithCapacityWork_spec (edges : Arcs V) (d : WeightedNetworkDemand V)
    (weight : V × V → ℕ × ℕ) (scale B : ℕ) (charges : V × V → ℕ)
    (each : ∀ e, (weight e).2 ≤ B) :
    let out := weightedNetworkViolationWithCapacityWork edges d weight scale charges
    let old := weightedNetworkViolationWithSearchWork edges d (fun e => (weight e).1) scale charges
    out.1 = old.1 ∧ out.2 ≤ old.2+edges.card*B := by
  obtain ⟨same,work⟩ := prepareWeightedCapacity_spec edges d weight charges scale B each
  simp only [weightedNetworkViolationWithCapacityWork,weightedNetworkViolationWithSearchWork,same,true_and]
  exact Nat.add_le_add_left work _

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
row per priced arc in each separator call. -/
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
    out.1 = old.1 ∧ out.2 ≤ old.2+D.length*(fuel*(edges.card*B)) := by
  let val := fun e => (weight e).1
  induction D generalizing charges with
  | nil => simp [weightedNetworkRunAtScaleWithCapacityWork,weightedNetworkRunAtScaleWithSearchWork]
  | cons d D ih =>
    let oldCheck := weightedNetworkViolationWithSearchWork edges d val scale
    let newCheck := weightedNetworkViolationWithCapacityWork edges d weight scale
    let oldFirst := weightedCoverLoopWithSearchWork oldCheck fuel charges
    let newFirst := weightedCoverLoopWithSearchWork newCheck fuel charges
    obtain ⟨firstEq,firstBound⟩ := weightedCoverLoop_compare oldCheck newCheck fuel (edges.card*B)
      (fun s => weightedNetworkViolationWithCapacityWork_spec edges d weight scale B s each) charges
    change newFirst.1 = oldFirst.1 at firstEq
    change newFirst.2 ≤ oldFirst.2+fuel*(edges.card*B) at firstBound
    obtain ⟨tailEq,tailBound⟩ := ih oldFirst.1.1
    let oldLast := weightedNetworkRunAtScaleWithSearchWork edges val scale fuel D oldFirst.1.1
    let newLast := weightedNetworkRunAtScaleWithCapacityWork edges weight scale fuel D oldFirst.1.1
    change newLast.1 = oldLast.1 at tailEq
    change newLast.2 ≤ oldLast.2+D.length*(fuel*(edges.card*B)) at tailBound
    change ((weightedNetworkRunAtScaleWithCapacityWork edges weight scale fuel D newFirst.1.1).1.1,
        newFirst.1.2++(weightedNetworkRunAtScaleWithCapacityWork edges weight scale fuel D newFirst.1.1).1.2) =
      (oldLast.1.1,oldFirst.1.2++oldLast.1.2) ∧
      newFirst.2+(weightedNetworkRunAtScaleWithCapacityWork edges weight scale fuel D newFirst.1.1).2 ≤
        oldFirst.2+oldLast.2+(D.length+1)*(fuel*(edges.card*B))
    rw [firstEq]
    change (newLast.1.1,oldFirst.1.2++newLast.1.2) = (oldLast.1.1,oldFirst.1.2++oldLast.1.2) ∧ _
    refine ⟨by rw [tailEq],?_⟩
    change newFirst.2+newLast.2 ≤ oldFirst.2+oldLast.2+(D.length+1)*(fuel*(edges.card*B))
    rw [Nat.add_mul]
    omega

end OnlineReachabilityPreservers
