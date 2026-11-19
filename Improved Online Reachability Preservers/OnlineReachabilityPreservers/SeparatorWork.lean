import OnlineReachabilityPreservers.RouteWork

/-! Search work inside integer flow separation. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V : Type*} [LinearOrder V] [Fintype V]

/-- The candidate visits and tests in one residual graph construction and
its shortest route search, for a graph with `n` vertices. -/
def residualStepWorkBound (n : ℕ) : ℕ :=
  n^2 + (n^2 * (2 * ((n + 1) * n * n^2)) + n * n^2) + 2 * n^2

private def residualPathWithWork (c f : ArcFlow V) (s t : V) : Option (List (V × V)) × ℕ :=
  let result := routePathWithSearchWork (residualArcs c f) s t
  (result.1, Fintype.card V ^ 2 + result.2.1 + result.2.2)

private theorem residualPathWithWork_spec (c f : ArcFlow V) (s t : V) :
    let result := residualPathWithWork c f s t
    result.1 = routePath (residualArcs c f) s t ∧ result.2 ≤ residualStepWorkBound (Fintype.card V) := by
  obtain ⟨path, scans, tests⟩ := routePathWithSearchWork_spec (residualArcs c f) s t
  refine ⟨path, ?_⟩
  let n := Fintype.card V
  let m := (residualArcs c f).card
  have size : m ≤ n ^ 2 := by
    simpa only [m, n, pow_two, Fintype.card_prod] using card_le_univ (residualArcs c f)
  have scanBound : m * (2 * ((n + 1) * n * m)) + n * m ≤
      n^2 * (2 * ((n + 1) * n * n^2)) + n * n^2 := by gcongr
  exact Nat.add_le_add (Nat.add_le_add_left (scans.trans scanBound) _) tests

/-- Repeat the ordinary integer augmentation while reporting residual
arc visits and path successor tests. The failed final search is counted. -/
def unitAugmentationsWithSearchWork (c : ArcFlow V) (s t : V) :
    ℕ → ArcFlow V → (ArcFlow V × ℕ) × ℕ
  | 0, f => ((f, 0), 0)
  | fuel + 1, f =>
    let first := residualPathWithWork c f s t
    match first.1 with
    | none => ((f, 0), first.2)
    | some path =>
      let rest := unitAugmentationsWithSearchWork c s t fuel (augmentArcFlow f path.toFinset)
      ((rest.1.1, rest.1.2 + 1), first.2 + rest.2)

theorem unitAugmentationsWithSearchWork_spec (c : ArcFlow V) (s t : V) (fuel : ℕ) (f : ArcFlow V) :
    let result := unitAugmentationsWithSearchWork c s t fuel f
    result.1 = unitAugmentations c s t fuel f ∧ result.2 ≤ fuel * residualStepWorkBound (Fintype.card V) := by
  induction fuel generalizing f with
  | zero => simp [unitAugmentationsWithSearchWork, unitAugmentations]
  | succ fuel ih =>
    let step := residualPathWithWork c f s t
    let B := residualStepWorkBound (Fintype.card V)
    obtain ⟨pathEq, stepCap⟩ := residualPathWithWork_spec c f s t
    change step.1 = _ at pathEq
    change step.2 ≤ B at stepCap
    cases route : step.1 with
    | none =>
      have same : routePath (residualArcs c f) s t = none := pathEq.symm.trans route
      simp only [unitAugmentationsWithSearchWork, unitAugmentations, ← show step =
        residualPathWithWork c f s t from rfl, route, same, true_and]
      exact stepCap.trans (by rw [Nat.succ_mul]; exact Nat.le_add_left _ _)
    | some path =>
      have same : routePath (residualArcs c f) s t = some path := pathEq.symm.trans route
      obtain ⟨restEq, restCap⟩ := ih (augmentArcFlow f path.toFinset)
      simp only [unitAugmentationsWithSearchWork, unitAugmentations, ← show step =
        residualPathWithWork c f s t from rfl, route, same, restEq, true_and]
      exact (Nat.add_le_add stepCap restCap).trans_eq
        ((Nat.add_comm _ _).trans (Nat.succ_mul fuel B).symm)

private def residualCutSideWithWork (c f : ArcFlow V) (s : V) : Finset V × ℕ :=
  let n := Fintype.card V
  let side := reachInWithArcInspections (reverseArcs (residualArcs c f)) s n
  (side.1, 2 * n^2 + side.2)

private theorem residualCutSideWithWork_spec (c f : ArcFlow V) (s : V) :
    let n := Fintype.card V
    let result := residualCutSideWithWork c f s
    result.1 = residualReach c f s ∧ result.2 ≤ 2 * n^2 + n * n^2 := by
  simp only [residualCutSideWithWork, reachInWithArcInspections_spec, residualReach, reaches,
    reverseArcs_card, true_and]
  have size : (residualArcs c f).card ≤ Fintype.card V ^ 2 := by
    simpa only [pow_two, Fintype.card_prod] using card_le_univ (residualArcs c f)
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ size) _

/-- The ordinary low-capacity cut, including the search that recovers its
source side when the augmentation stops early. -/
def findLowCapacityCutWithSearchWork (c : ArcFlow V) (s t : V) (supply : ℕ) : Option (Finset V) × ℕ :=
  let aug := unitAugmentationsWithSearchWork c s t supply (fun _ => 0)
  if aug.1.2 = supply then (none, aug.2)
  else
    let side := residualCutSideWithWork c aug.1.1 s
    (some side.1, aug.2 + side.2)

theorem findLowCapacityCutWithSearchWork_spec (c : ArcFlow V) (s t : V) (supply : ℕ) :
    let n := Fintype.card V
    let result := findLowCapacityCutWithSearchWork c s t supply
    result.1 = findLowCapacityCut c s t supply ∧
      result.2 ≤ supply * residualStepWorkBound n + (2 * n^2 + n * n^2) := by
  let aug := unitAugmentationsWithSearchWork c s t supply (fun _ => 0)
  let raw := unitAugmentations c s t supply (fun _ => 0)
  obtain ⟨same, work⟩ := unitAugmentationsWithSearchWork_spec c s t supply (fun _ => 0)
  obtain ⟨side, finish⟩ := residualCutSideWithWork_spec c aug.1.1 s
  change aug.1 = raw at same
  change aug.2 ≤ _ at work
  by_cases enough : raw.2 = supply
  · simpa only [findLowCapacityCutWithSearchWork, findLowCapacityCut, ← show aug =
      unitAugmentationsWithSearchWork c s t supply (fun _ => 0) from rfl, ← show raw =
      unitAugmentations c s t supply (fun _ => 0) from rfl, same, enough, ite_true, true_and] using
        work.trans (Nat.le_add_right _ (2 * Fintype.card V^2 + Fintype.card V * Fintype.card V^2))
  · rw [same] at side finish
    simp only [findLowCapacityCutWithSearchWork, findLowCapacityCut, ← show aug =
      unitAugmentationsWithSearchWork c s t supply (fun _ => 0) from rfl, ← show raw =
      unitAugmentations c s t supply (fun _ => 0) from rfl,
      same, enough, ite_false, side, true_and]
    exact Nat.add_le_add work finish

/-- The metered thin separator shares the interval before evaluating capacities.
The additional term budgets arc inspections in the two reachability searches
and the interval filter. It excludes the underlying finite container costs. -/
def fastThinViolationWithSearchWork (G : Arcs V) (d : V × V) (load : CutLoads V)
    : Option (Finset V) × ℕ :=
  if d.1 = d.2 then (none, 0)
  else
    let interval := reachInterval G d
    let edges := G.filter (fun e => e.1 ∈ interval ∧ e.2 ∈ interval)
    let cap : ArcFlow V := fun e => if e ∈ edges then (2 : ℤ) ^ load e else 0
    let result := findLowCapacityCutWithSearchWork cap d.1 d.2 G.card
    (result.1.map (· ∩ interval), result.2 + (2 * Fintype.card V * G.card + G.card))

private theorem fastThinViolation_eq_lowCut (G : Arcs V) (d : V × V) (load : CutLoads V) (hne : d.1 ≠ d.2) :
    fastThinViolation G d load = (findLowCapacityCut (localArcCapacity G d load) d.1 d.2 G.card).map
      (· ∩ reachInterval G d) := by
  let c := localArcCapacity G d load
  let r := unitAugmentations c d.1 d.2 G.card (fun _ => 0)
  have plain : fastThinViolation G d load =
      if r.2 = G.card then none else some (residualReach c r.1 d.1 ∩ reachInterval G d) := by
    simp only [fastThinViolation, hne, ite_false]
    rfl
  rw [plain]
  change (if r.2 = G.card then none else some (residualReach c r.1 d.1 ∩ reachInterval G d)) =
    (if r.2 = G.card then none else some (residualReach c r.1 d.1)).map (· ∩ reachInterval G d)
  split <;> rfl

theorem fastThinViolationWithSearchWork_spec (G : Arcs V) (d : V × V) (load : CutLoads V) :
    let n := Fintype.card V
    let result := fastThinViolationWithSearchWork G d load
    result.1 = fastThinViolation G d load ∧ result.2 ≤
      G.card * residualStepWorkBound n + (2 * n^2 + n * n^2) + (2 * n * G.card + G.card) := by
  by_cases h : d.1 = d.2
  · simp [fastThinViolationWithSearchWork, fastThinViolation, h]
  · obtain ⟨same, work⟩ := findLowCapacityCutWithSearchWork_spec (localArcCapacity G d load) d.1 d.2 G.card
    simp only [fastThinViolationWithSearchWork, h, ite_false, fastThinViolation_eq_lowCut G d load h]
    change (findLowCapacityCutWithSearchWork (localArcCapacity G d load) d.1 d.2 G.card).1.map _ = _ ∧
      (findLowCapacityCutWithSearchWork (localArcCapacity G d load) d.1 d.2 G.card).2 + _ ≤ _
    exact ⟨congrArg (Option.map (· ∩ reachInterval G d)) same, Nat.add_le_add_right work _⟩

/-- A weighted separator with its residual work and the final outgoing-cut filter. -/
def weightedNetworkViolationWithSearchWork (edges : Arcs V) (d : WeightedNetworkDemand V)
    (weight : V × V → ℕ) (scale : ℕ) (charges : V × V → ℕ) : Option (Arcs V) × ℕ :=
  let result := findLowCapacityCutWithSearchWork
    (weightedNetworkCapacity edges d weight charges scale) d.source d.sink scale
  (result.1.map (outgoingCut edges), result.2 + edges.card)

theorem weightedNetworkViolationWithSearchWork_spec (edges : Arcs V) (d : WeightedNetworkDemand V)
    (weight : V × V → ℕ) (scale : ℕ) (charges : V × V → ℕ) :
    let n := Fintype.card V
    let result := weightedNetworkViolationWithSearchWork edges d weight scale charges
    result.1 = weightedNetworkViolation edges d weight scale charges ∧ result.2 ≤
      scale * residualStepWorkBound n + (2 * n^2 + n * n^2) + edges.card := by
  obtain ⟨same, work⟩ := findLowCapacityCutWithSearchWork_spec
    (weightedNetworkCapacity edges d weight charges scale) d.source d.sink scale
  exact ⟨congrArg (Option.map (outgoingCut edges)) same, Nat.add_le_add_right work _⟩

section CuttingLoop

variable {E : Type*} [DecidableEq E]

/-- Sum the work reported by the separator on the cuts actually tested. -/
def weightedCoverLoopWithSearchWork (search : (E → ℕ) → Option (Finset E) × ℕ) :
    ℕ → (E → ℕ) → ((E → ℕ) × List (Finset E)) × ℕ
  | 0, charges => ((charges, []), 0)
  | fuel + 1, charges =>
    let first := search charges
    match first.1 with
    | none => ((charges, []), first.2)
    | some cut =>
      let out := weightedCoverLoopWithSearchWork search fuel (chargeWeightedCut cut charges)
      ((out.1.1, cut :: out.1.2), first.2 + out.2)

theorem weightedCoverLoopWithSearchWork_spec (search : (E → ℕ) → Option (Finset E) × ℕ)
    (fuel budget : ℕ) (charges : E → ℕ) (cap : ∀ state, (search state).2 ≤ budget) :
    let result := weightedCoverLoopWithSearchWork search fuel charges
    result.1 = weightedCoverLoop (fun state => (search state).1) fuel charges ∧ result.2 ≤ fuel*budget := by
  induction fuel generalizing charges with
  | zero => simp [weightedCoverLoopWithSearchWork, weightedCoverLoop]
  | succ fuel ih =>
    cases answer : (search charges).1 with
    | none =>
      simp only [weightedCoverLoopWithSearchWork, weightedCoverLoop, answer, true_and]
      exact (cap charges).trans (by rw [Nat.succ_mul]; exact Nat.le_add_left _ _)
    | some cut =>
      obtain ⟨out, work⟩ := ih (chargeWeightedCut cut charges)
      simp only [weightedCoverLoopWithSearchWork, weightedCoverLoop, answer, out, true_and]
      exact (Nat.add_le_add (cap charges) work).trans_eq
        ((Nat.add_comm _ _).trans (Nat.succ_mul fuel budget).symm)

end CuttingLoop

/-- Bound the residual vertex-pair inspections, route tests and cut filter
for one weighted separator call with the given scale. -/
def weightedSeparatorWorkBound (vertices edges scale : ℕ) : ℕ :=
  scale * residualStepWorkBound vertices + (2 * vertices^2 + vertices * vertices^2) + edges

/-- Execute the same weighted network updates with the inner separator work. -/
def weightedNetworkRunWithSearchWork (edges : Arcs V) (weight : V × V → ℕ) :
    List (WeightedNetworkDemand V) → (V × V → ℕ) → ((V × V → ℕ) × List (Arcs V)) × ℕ
  | [], initial => ((initial, []), 0)
  | d :: D, initial =>
    let first := weightedCoverLoopWithSearchWork
      (weightedNetworkViolationWithSearchWork edges d weight (weightedCoverScale edges weight))
      (weightedCoverFuel edges weight) initial
    let last := weightedNetworkRunWithSearchWork edges weight D first.1.1
    ((last.1.1, first.1.2 ++ last.1.2), first.2 + last.2)

theorem weightedNetworkRunWithSearchWork_spec (edges : Arcs V) (weight : V × V → ℕ)
    (D : List (WeightedNetworkDemand V)) (initial : V × V → ℕ) :
    let result := weightedNetworkRunWithSearchWork edges weight D initial
    let single := weightedSeparatorWorkBound (Fintype.card V) edges.card (weightedCoverScale edges weight)
    result.1 = weightedNetworkRun edges weight D initial ∧
      result.2 ≤ D.length * (weightedCoverFuel edges weight * single) := by
  let scale := weightedCoverScale edges weight
  let budget := weightedSeparatorWorkBound (Fintype.card V) edges.card scale
  let fuel := weightedCoverFuel edges weight
  induction D generalizing initial with
  | nil => simp [weightedNetworkRunWithSearchWork, weightedNetworkRun]
  | cons d D ih =>
    let separate := weightedNetworkViolationWithSearchWork edges d weight scale
    let first := weightedCoverLoopWithSearchWork separate fuel initial
    have each (state : V × V → ℕ) : (separate state).2 ≤ budget :=
      (weightedNetworkViolationWithSearchWork_spec edges d weight scale state).2
    have same : (fun state => (separate state).1) = weightedNetworkViolation edges d weight scale :=
      funext fun state => (weightedNetworkViolationWithSearchWork_spec edges d weight scale state).1
    obtain ⟨firstEq, firstWork⟩ := weightedCoverLoopWithSearchWork_spec separate fuel budget initial each
    change first.1 = _ at firstEq
    rw [same] at firstEq
    change first.1 = weightedNetworkStep edges weight d initial at firstEq
    obtain ⟨lastEq, lastWork⟩ := ih first.1.1
    change ((weightedNetworkRunWithSearchWork edges weight D first.1.1).1.1,
        first.1.2 ++ (weightedNetworkRunWithSearchWork edges weight D first.1.1).1.2) =
      weightedNetworkRun edges weight (d :: D) initial ∧
      first.2 + (weightedNetworkRunWithSearchWork edges weight D first.1.1).2 ≤ (D.length+1)*(fuel*budget)
    refine ⟨?_, ?_⟩
    · rw [lastEq, firstEq]
      rfl
    · exact (Nat.add_le_add firstWork lastWork).trans_eq
        ((Nat.add_comm _ _).trans (Nat.succ_mul D.length (fuel*budget)).symm)

/-- Meter the weighted separators in one fractional run on the paired forest. -/
def forestFractionalRunWithSearchWork (G : Arcs V) (height : ℕ) (D : List (V × V)) :
    ((ForestNetworkVertex V height × ForestNetworkVertex V height → ℕ) ×
      List (Arcs (ForestNetworkVertex V height))) × ℕ :=
  weightedNetworkRunWithSearchWork (forestNetworkPriced G (heightForest G height)) (forestNetworkWeight G)
    (D.map (forestNetworkDemand G height)) (fun _ => 0)

theorem forestFractionalRunWithSearchWork_spec (G : Arcs V) (height : ℕ) (D : List (V × V)) :
    let B := max 1 (Fintype.card V * Fintype.card (HeightForestVertex V height)^2)
    let N := Fintype.card (ForestNetworkVertex V height)
    let result := forestFractionalRunWithSearchWork G height D
    result.1 = forestFractionalRun G height D ∧
      result.2 ≤ D.length * (((B+1)*B+1)*weightedSeparatorWorkBound N (N^2) B) := by
  let B := max 1 (Fintype.card V * Fintype.card (HeightForestVertex V height)^2)
  let N := Fintype.card (ForestNetworkVertex V height)
  let edges := forestNetworkPriced G (heightForest G height)
  let weight := forestNetworkWeight (height := height) G
  let scale := weightedCoverScale edges weight
  have scaleCap : scale ≤ B := forestNetworkScale_le G height
  have edgeCap : edges.card ≤ N^2 := by
    simpa only [pow_two, Fintype.card_prod, N] using card_le_univ edges
  have fuelCap : weightedCoverFuel edges weight ≤ (B+1)*B+1 := by
    apply Nat.add_le_add_right
    apply Nat.mul_le_mul
    · exact Nat.succ_le_succ ((Nat.log2_le_self _).trans scaleCap)
    · exact (le_max_right _ _).trans scaleCap
  have searchCap : weightedSeparatorWorkBound N edges.card scale ≤ weightedSeparatorWorkBound N (N^2) B := by
    unfold weightedSeparatorWorkBound
    gcongr
  obtain ⟨same, work⟩ := weightedNetworkRunWithSearchWork_spec edges weight
    (D.map (forestNetworkDemand G height)) (fun _ => 0)
  refine ⟨same, ?_⟩
  rw [List.length_map] at work
  exact work.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul fuelCap searchCap))

end OnlineReachabilityPreservers
