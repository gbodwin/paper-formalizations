import OnlineReachabilityPreservers.RouteWork

/-! Search work inside integer flow separation. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V : Type*} [LinearOrder V] [Fintype V]

private def residualRouteWorkBound (n : ℕ) : ℕ :=
  (n^2 * (2 * ((n + 1) * n * n^2)) + n * n^2) + 2 * n^2

/-- The candidate visits and tests in one residual graph construction and
its shortest route search, for a graph with `n` vertices. -/
def residualStepWorkBound (n : ℕ) : ℕ :=
  n^2 + (n^2 * (2 * ((n + 1) * n * n^2)) + n * n^2) + 2 * n^2

private def residualPathWithWork (build : ArcFlow V → Arcs V × ℕ)
    (f : ArcFlow V) (s t : V) : Option (List (V × V)) × ℕ :=
  let graph := build f
  let result := routePathWithSearchWork graph.1 s t
  (result.1, graph.2 + result.2.1 + result.2.2)

private theorem residualPathWithWork_spec (build : ArcFlow V → Arcs V × ℕ)
    (c f : ArcFlow V) (s t : V) (same : (build f).1 = residualArcs c f) (B : ℕ)
    (buildBound : (build f).2 ≤ B) :
    let result := residualPathWithWork build f s t
    result.1 = routePath (residualArcs c f) s t ∧ result.2 ≤ B + residualRouteWorkBound (Fintype.card V) := by
  obtain ⟨path, scans, tests⟩ := routePathWithSearchWork_spec (build f).1 s t
  refine ⟨path.trans (congrArg (fun edges => routePath edges s t) same), ?_⟩
  let n := Fintype.card V
  let m := (build f).1.card
  have size : m ≤ n ^ 2 := by
    simpa only [m, n, pow_two, Fintype.card_prod] using card_le_univ (build f).1
  have scanBound : m * (2 * ((n + 1) * n * m)) + n * m ≤
      n^2 * (2 * ((n + 1) * n * n^2)) + n * n^2 := by gcongr
  simpa only [residualPathWithWork, residualRouteWorkBound, Nat.add_assoc] using
    Nat.add_le_add (Nat.add_le_add buildBound (scans.trans scanBound)) tests

/-- Repeat integer augmentation with a metered residual graph constructor.
The failed final search is counted. -/
private def unitAugmentationsWithResidualWork (build : ArcFlow V → Arcs V × ℕ) (s t : V) :
    ℕ → ArcFlow V → (ArcFlow V × ℕ) × ℕ
  | 0, f => ((f, 0), 0)
  | fuel + 1, f =>
    let first := residualPathWithWork build f s t
    match first.1 with
    | none => ((f, 0), first.2)
    | some path =>
      let rest := unitAugmentationsWithResidualWork build s t fuel (augmentArcFlow f path.toFinset)
      ((rest.1.1, rest.1.2 + 1), first.2 + rest.2)

private theorem unitAugmentationsWithResidualWork_spec (build : ArcFlow V → Arcs V × ℕ)
    (c : ArcFlow V) (s t : V) (fuel : ℕ) (f : ArcFlow V) (B : ℕ)
    (each : ∀ flow, (build flow).1 = residualArcs c flow ∧ (build flow).2 ≤ B) :
    let result := unitAugmentationsWithResidualWork build s t fuel f
    result.1 = unitAugmentations c s t fuel f ∧
      result.2 ≤ fuel * (B + residualRouteWorkBound (Fintype.card V)) := by
  induction fuel generalizing f with
  | zero => simp [unitAugmentationsWithResidualWork, unitAugmentations]
  | succ fuel ih =>
    let step := residualPathWithWork build f s t
    let stepBound := B + residualRouteWorkBound (Fintype.card V)
    obtain ⟨pathEq, stepCap⟩ := residualPathWithWork_spec build c f s t (each f).1 B (each f).2
    change step.1 = _ at pathEq
    change step.2 ≤ stepBound at stepCap
    cases route : step.1 with
    | none =>
      have same : routePath (residualArcs c f) s t = none := pathEq.symm.trans route
      simp only [unitAugmentationsWithResidualWork, unitAugmentations, ← show step =
        residualPathWithWork build f s t from rfl, route, same, true_and]
      exact stepCap.trans (by rw [Nat.succ_mul]; exact Nat.le_add_left _ _)
    | some path =>
      have same : routePath (residualArcs c f) s t = some path := pathEq.symm.trans route
      obtain ⟨restEq, restCap⟩ := ih (augmentArcFlow f path.toFinset)
      simp only [unitAugmentationsWithResidualWork, unitAugmentations, ← show step =
        residualPathWithWork build f s t from rfl, route, same, restEq, true_and]
      exact (Nat.add_le_add stepCap restCap).trans_eq
        ((Nat.add_comm _ _).trans (Nat.succ_mul fuel stepBound).symm)

private def residualGraphWithPairVisits (c f : ArcFlow V) : Arcs V × ℕ :=
  (residualArcs c f, Fintype.card V ^ 2)

/-- Repeat the ordinary integer augmentation while reporting residual
arc visits and path successor tests. -/
def unitAugmentationsWithSearchWork (c : ArcFlow V) (s t : V) (fuel : ℕ) (f : ArcFlow V) :
    (ArcFlow V × ℕ) × ℕ :=
  unitAugmentationsWithResidualWork (residualGraphWithPairVisits c) s t fuel f

theorem unitAugmentationsWithSearchWork_spec (c : ArcFlow V) (s t : V) (fuel : ℕ) (f : ArcFlow V) :
    let result := unitAugmentationsWithSearchWork c s t fuel f
    result.1 = unitAugmentations c s t fuel f ∧ result.2 ≤ fuel * residualStepWorkBound (Fintype.card V) := by
  simpa only [unitAugmentationsWithSearchWork, residualStepWorkBound, residualRouteWorkBound, Nat.add_assoc]
    using unitAugmentationsWithResidualWork_spec (residualGraphWithPairVisits c) c s t fuel f
      (Fintype.card V^2) (fun _ => ⟨rfl,le_rfl⟩)

private def residualCutSideWithWork (build : ArcFlow V → Arcs V × ℕ)
    (f : ArcFlow V) (s : V) : Finset V × ℕ :=
  let n := Fintype.card V
  let graph := build f
  let side := reachInWithArcInspections (reverseArcs graph.1) s n
  (side.1, graph.2 + n^2 + side.2)

private theorem residualCutSideWithWork_spec (build : ArcFlow V → Arcs V × ℕ)
    (c f : ArcFlow V) (s : V) (same : (build f).1 = residualArcs c f)
    (B : ℕ) (buildBound : (build f).2 ≤ B) :
    let n := Fintype.card V
    let result := residualCutSideWithWork build f s
    result.1 = residualReach c f s ∧ result.2 ≤ B + (n^2 + n * n^2) := by
  simp only [residualCutSideWithWork, reachInWithArcInspections_spec, same, residualReach, reaches,
    reverseArcs_card, true_and]
  have size : (residualArcs c f).card ≤ Fintype.card V ^ 2 := by
    simpa only [pow_two, Fintype.card_prod] using card_le_univ (residualArcs c f)
  simpa only [Nat.add_assoc] using
    Nat.add_le_add (Nat.add_le_add_right buildBound _) (Nat.mul_le_mul_left _ size)

/-- Charge residual graph construction, route searches, and the final
source-side search when the augmentation stops early. -/
def findLowCapacityCutWithResidualWork (build : ArcFlow V → Arcs V × ℕ)
    (s t : V) (supply : ℕ) : Option (Finset V) × ℕ :=
  let aug := unitAugmentationsWithResidualWork build s t supply (fun _ => 0)
  if aug.1.2 = supply then (none, aug.2)
  else
    let side := residualCutSideWithWork build aug.1.1 s
    (some side.1, aug.2 + side.2)

theorem findLowCapacityCutWithResidualWork_spec (build : ArcFlow V → Arcs V × ℕ)
    (c : ArcFlow V) (s t : V) (supply extra : ℕ)
    (each : ∀ flow, (build flow).1 = residualArcs c flow ∧ (build flow).2 ≤ Fintype.card V^2 + extra) :
    let n := Fintype.card V
    let result := findLowCapacityCutWithResidualWork build s t supply
    result.1 = findLowCapacityCut c s t supply ∧
      result.2 ≤ supply * residualStepWorkBound n + (2 * n^2 + n * n^2) + (supply+1)*extra := by
  let n := Fintype.card V
  let aug := unitAugmentationsWithResidualWork build s t supply (fun _ => 0)
  let raw := unitAugmentations c s t supply (fun _ => 0)
  obtain ⟨same, work⟩ := unitAugmentationsWithResidualWork_spec build c s t supply (fun _ => 0)
    (n^2+extra) each
  obtain ⟨side, finish⟩ := residualCutSideWithWork_spec build c aug.1.1 s (each _).1 (n^2+extra) (each _).2
  change aug.1 = raw at same
  have workTotal : supply * (n^2 + extra + residualRouteWorkBound n) +
      (n^2 + extra + (n^2 + n*n^2)) =
      supply * residualStepWorkBound n + (2*n^2 + n*n^2) + (supply+1)*extra := by
    simp only [residualRouteWorkBound, residualStepWorkBound]
    ring
  by_cases enough : raw.2 = supply
  · simp only [findLowCapacityCutWithResidualWork, findLowCapacityCut, ← show aug =
      unitAugmentationsWithResidualWork build s t supply (fun _ => 0) from rfl, ← show raw =
      unitAugmentations c s t supply (fun _ => 0) from rfl, same, enough, ite_true, true_and]
    exact work.trans ((Nat.le_add_right _ _).trans_eq workTotal)
  · rw [same] at side finish
    simp only [findLowCapacityCutWithResidualWork, findLowCapacityCut, ← show aug =
      unitAugmentationsWithResidualWork build s t supply (fun _ => 0) from rfl, ← show raw =
      unitAugmentations c s t supply (fun _ => 0) from rfl,
      same, enough, ite_false, side, true_and]
    exact (Nat.add_le_add work finish).trans_eq workTotal

/-- The ordinary low-capacity cut, including the search that recovers its
source side when the augmentation stops early. -/
def findLowCapacityCutWithSearchWork (c : ArcFlow V) (s t : V) (supply : ℕ) : Option (Finset V) × ℕ :=
  findLowCapacityCutWithResidualWork (residualGraphWithPairVisits c) s t supply

theorem findLowCapacityCutWithResidualWork_eq (build : ArcFlow V → Arcs V × ℕ)
    (c : ArcFlow V) (s t : V) (supply : ℕ)
    (same : ∀ f, build f = (residualArcs c f, Fintype.card V^2)) :
    findLowCapacityCutWithResidualWork build s t supply = findLowCapacityCutWithSearchWork c s t supply := by
  rw [show build = residualGraphWithPairVisits c from funext same]
  rfl

theorem findLowCapacityCutWithSearchWork_spec (c : ArcFlow V) (s t : V) (supply : ℕ) :
    let n := Fintype.card V
    let result := findLowCapacityCutWithSearchWork c s t supply
    result.1 = findLowCapacityCut c s t supply ∧
      result.2 ≤ supply * residualStepWorkBound n + (2 * n^2 + n * n^2) := by
  simpa only [findLowCapacityCutWithSearchWork, Nat.mul_zero, Nat.add_zero] using
    findLowCapacityCutWithResidualWork_spec (residualGraphWithPairVisits c) c s t supply 0
      (fun _ => ⟨rfl,le_rfl⟩)

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

/-- Evaluate each request using the fixed scale and fuel for the input weights. -/
def weightedNetworkRunAtScaleWithSearchWork (edges : Arcs V) (weight : V × V → ℕ) (scale fuel : ℕ) :
    List (WeightedNetworkDemand V) → (V × V → ℕ) → ((V × V → ℕ) × List (Arcs V)) × ℕ
  | [], initial => ((initial, []), 0)
  | d :: D, initial =>
    let first := weightedCoverLoopWithSearchWork
      (weightedNetworkViolationWithSearchWork edges d weight scale) fuel initial
    let last := weightedNetworkRunAtScaleWithSearchWork edges weight scale fuel D first.1.1
    ((last.1.1, first.1.2 ++ last.1.2), first.2 + last.2)

/-- Execute the same weighted network updates with the inner separator work. -/
def weightedNetworkRunWithSearchWork (edges : Arcs V) (weight : V × V → ℕ) :
    List (WeightedNetworkDemand V) → (V × V → ℕ) → ((V × V → ℕ) × List (Arcs V)) × ℕ :=
  weightedNetworkRunAtScaleWithSearchWork edges weight (weightedCoverScale edges weight) (weightedCoverFuel edges weight)

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
  | nil => simp [weightedNetworkRunWithSearchWork, weightedNetworkRunAtScaleWithSearchWork, weightedNetworkRun]
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

abbrev FinArcFlowTable (n : ℕ) := { values : Array ℤ // values.size = n * n }

@[inline] private def finFlowPosition {n : ℕ} (arc : Fin n × Fin n) : Fin (n * n) :=
  ⟨arc.2.val + n * arc.1.val, (finProdFinEquiv arc).isLt⟩

@[inline] def FinArcFlowTable.read {n : ℕ} (table : FinArcFlowTable n) : ArcFlow (Fin n) :=
  fun arc =>
    let position := finFlowPosition arc
    table.val[position.val]'(by rw [table.property]; exact position.isLt)

@[inline] private def FinArcFlowTable.addAt {n : ℕ} (table : FinArcFlowTable n)
    (arc : Fin n × Fin n) (delta : ℤ) : FinArcFlowTable n :=
  let position := finFlowPosition arc
  have fits : position.val < table.val.size := by rw [table.property]; exact position.isLt
  let value := table.val[position.val]'fits
  ⟨table.val.set position.val (value + delta) fits, by simpa using table.property⟩

private theorem FinArcFlowTable.read_addAt {n : ℕ} (table : FinArcFlowTable n)
    (arc query : Fin n × Fin n) (delta : ℤ) :
    (table.addAt arc delta).read query = table.read query + if query = arc then delta else 0 := by
  unfold FinArcFlowTable.addAt FinArcFlowTable.read
  simp only [Array.getElem_set]
  simp only [show (finFlowPosition arc).val = (finFlowPosition query).val ↔ query = arc from
    ⟨fun same => (finProdFinEquiv.injective (Fin.ext same)).symm, fun same => by subst query; rfl⟩]
  split <;> simp_all

def zeroFinArcFlowTable (n : ℕ) : FinArcFlowTable n :=
  ⟨Array.replicate (n * n) 0, by simp⟩

theorem zeroFinArcFlowTable_read (n : ℕ) : (zeroFinArcFlowTable n).read = fun _ => 0 := by
  funext arc
  simp [FinArcFlowTable.read, zeroFinArcFlowTable]

private def augmentFinArcFlowOnList {n : ℕ} (table : FinArcFlowTable n)
    (path : List (Fin n × Fin n)) (work : ℕ) : FinArcFlowTable n × ℕ :=
  match path with
  | [] => (table, work + 2)
  | arc :: tail =>
    let onward := table.addAt arc 1
    let next := onward.addAt arc.swap (-1)
    augmentFinArcFlowOnList next tail (work + 20)

private theorem augmentFinArcFlowOnList_spec {n : ℕ} (table : FinArcFlowTable n)
    (path : List (Fin n × Fin n)) (work : ℕ) :
    let result := augmentFinArcFlowOnList table path work
    (∀ e, result.1.read e = table.read e + (path.count e : ℤ) - (path.count e.swap : ℤ)) ∧
      result.2 = work + 20 * path.length + 2 := by
  induction path generalizing table work with
  | nil => simp [augmentFinArcFlowOnList]
  | cons arc path ih =>
    let next := (table.addAt arc 1).addAt arc.swap (-1)
    obtain ⟨values, tally⟩ := ih next (work + 20)
    refine ⟨?_, ?_⟩
    · intro e
      rw [augmentFinArcFlowOnList]
      change (augmentFinArcFlowOnList next path (work + 20)).1.read e = _
      rw [values, FinArcFlowTable.read_addAt, FinArcFlowTable.read_addAt]
      rw [List.count_cons, List.count_cons]
      have swapEq : e = arc.swap ↔ arc = e.swap := by
        constructor
        · intro eq
          rw [eq, Prod.swap_swap]
        · intro eq
          rw [eq, Prod.swap_swap]
      have eqF : (arc == e) = true ↔ e = arc := beq_iff_eq.trans eq_comm
      have eqR : (arc == e.swap) = true ↔ e = arc.swap := beq_iff_eq.trans swapEq.symm
      have castAdd (count : ℕ) (chosen : Prop) [Decidable chosen] :
          ((count + (if chosen then 1 else 0) : ℕ) : ℤ) = (count : ℤ) + if chosen then 1 else 0 := by
        split <;> norm_cast
      have negIndicator : (if e = arc.swap then -1 else 0 : ℤ) = -(if e = arc.swap then 1 else 0) := by
        split <;> simp
      simp only [eqF, eqR, castAdd, negIndicator]
      ring
    · rw [augmentFinArcFlowOnList]
      change (augmentFinArcFlowOnList next path (work + 20)).2 = _
      rw [tally, List.length_cons]
      omega

/-- Update both signed entries for each arc and count the indexed operations. -/
def augmentFinArcFlowWithWordWork {n : ℕ} (table : FinArcFlowTable n)
    (path : List (Fin n × Fin n)) : FinArcFlowTable n × ℕ :=
  augmentFinArcFlowOnList table path 0

theorem augmentFinArcFlowWithWordWork_spec {n : ℕ} (table : FinArcFlowTable n)
    (path : List (Fin n × Fin n)) (simple : path.Nodup) :
    let result := augmentFinArcFlowWithWordWork table path
    result.1.read = augmentArcFlow table.read path.toFinset ∧
      result.2 = 20 * path.length + 2 := by
  obtain ⟨values, tally⟩ := augmentFinArcFlowOnList_spec table path 0
  refine ⟨?_, by simpa [augmentFinArcFlowWithWordWork] using tally⟩
  funext e
  rw [augmentFinArcFlowWithWordWork, values]
  have one (a : Fin n × Fin n) : (path.count a : ℤ) = if a ∈ path.toFinset then 1 else 0 := by
    simp only [List.mem_toFinset]
    by_cases mem : a ∈ path
    · have count : path.count a = 1 := List.count_eq_one_of_mem simple mem
      simp [mem, count]
    · simp [mem, List.count_eq_zero.mpr mem]
  rw [one, one]
  rfl

private theorem routedPathBound {n : ℕ} (G : Arcs (Fin n)) (s t : Fin n)
    (path : List (Fin n × Fin n)) (selected : routePath G s t = some path) :
    path.Nodup ∧ path.length ≤ n := by
  have simple := (routePath_some selected).2
  have heads : (path.map Prod.fst).Nodup := (List.sublist_append_left ..).nodup simple
  have count := card_le_univ ((path.map Prod.fst).toFinset)
  rw [List.toFinset_card_of_nodup heads, List.length_map, Fintype.card_fin] at count
  exact ⟨List.Nodup.of_map Prod.fst heads, count⟩

/-- Keep the selected routes while storing the augmenting flow in a signed table. -/
def unitAugmentationsWithDenseFlowWork {n : ℕ} (capacity : ArcFlow (Fin n)) (s t : Fin n) :
    ℕ → FinArcFlowTable n → (FinArcFlowTable n × ℕ) × ℕ × ℕ
  | 0, table => ((table, 0), 0, 2)
  | fuel + 1, table =>
    let selected := routePathWithSearchWork (residualArcs capacity table.read) s t
    let search := n ^ 2 + selected.2.1 + selected.2.2
    match selected.1 with
    | none => ((table, 0), search, 5)
    | some path =>
      let changed := augmentFinArcFlowWithWordWork table path
      let rest := unitAugmentationsWithDenseFlowWork capacity s t fuel changed.1
      ((rest.1.1, rest.1.2 + 1), search + rest.2.1, changed.2 + rest.2.2 + 8)

theorem unitAugmentationsWithDenseFlowWork_spec {n : ℕ} (capacity : ArcFlow (Fin n)) (s t : Fin n)
    (fuel : ℕ) (table : FinArcFlowTable n) :
    let result := unitAugmentationsWithDenseFlowWork capacity s t fuel table
    (result.1.1.read, result.1.2) = unitAugmentations capacity s t fuel table.read ∧
      result.2.1 ≤ fuel * residualStepWorkBound n ∧
      result.2.2 ≤ result.1.2 * (20 * n + 10) + 5 := by
  induction fuel generalizing table with
  | zero => simp [unitAugmentationsWithDenseFlowWork, unitAugmentations]
  | succ fuel ih =>
    let graph := residualArcs capacity table.read
    let result := routePathWithSearchWork graph s t
    have cap : graph.card ≤ n ^ 2 := by
      simpa [pow_two, Fintype.card_prod] using card_le_univ graph
    obtain ⟨exactPath, scans, tests⟩ := routePathWithSearchWork_spec graph s t
    change result.1 = routePath graph s t at exactPath
    have charged : n ^ 2 + result.2.1 + result.2.2 ≤ residualStepWorkBound n := by
      unfold residualStepWorkBound
      rw [Fintype.card_fin] at scans tests
      apply Nat.add_le_add (Nat.add_le_add_left (scans.trans ?_) _) tests
      gcongr
    cases returned : result.1 with
    | none =>
      have plain : routePath graph s t = none := exactPath.symm.trans returned
      change (routePathWithSearchWork graph s t).1 = none at returned
      simp only [unitAugmentationsWithDenseFlowWork, unitAugmentations,
        ← show graph = residualArcs capacity table.read from rfl, returned, plain]
      refine ⟨trivial, ?_, by simp⟩
      change n ^ 2 + result.2.1 + result.2.2 ≤ (fuel + 1) * residualStepWorkBound n
      exact charged.trans (by rw [Nat.add_mul fuel 1, Nat.one_mul]; exact Nat.le_add_left _ _)
    | some path =>
      have plain : routePath graph s t = some path := exactPath.symm.trans returned
      obtain ⟨nodup, short⟩ := routedPathBound graph s t path plain
      let changed := augmentFinArcFlowWithWordWork table path
      obtain ⟨same, updateWork⟩ := augmentFinArcFlowWithWordWork_spec table path nodup
      obtain ⟨tail, searchBound, updateBound⟩ := ih changed.1
      let rest := unitAugmentationsWithDenseFlowWork capacity s t fuel changed.1
      change (rest.1.1.read, rest.1.2) = unitAugmentations capacity s t fuel changed.1.read at tail
      change changed.1.read = augmentArcFlow table.read path.toFinset at same
      change changed.2 = 20 * path.length + 2 at updateWork
      change (routePathWithSearchWork graph s t).1 = some path at returned
      simp only [unitAugmentationsWithDenseFlowWork, unitAugmentations,
        ← show graph = residualArcs capacity table.read from rfl, returned, plain]
      change (rest.1.1.read, rest.1.2 + 1) = _ ∧
        (n ^ 2 + result.2.1 + result.2.2) + rest.2.1 ≤ (fuel + 1) * residualStepWorkBound n ∧
        changed.2 + rest.2.2 + 8 ≤ (rest.1.2 + 1) * (20 * n + 10) + 5
      refine ⟨?_, ?_, ?_⟩
      · rw [← same, ← tail]
      · exact (Nat.add_le_add charged searchBound).trans_eq
          ((Nat.add_comm ..).trans (Nat.succ_mul ..).symm)
      · change rest.2.2 ≤ rest.1.2 * (20 * n + 10) + 5 at updateBound
        rw [updateWork, Nat.add_mul rest.1.2 1, Nat.one_mul]
        omega

private def fillArrayWithWordWork {α : Type*} (value : α) : ℕ → Array α → ℕ → Array α × ℕ
  | 0, table, work => (table, work + 2)
  | k + 1, table, work => fillArrayWithWordWork value k (table.push value) (work + 4)

private theorem fillArrayWithWordWork_spec {α : Type*} (value : α) (count : ℕ) (table : Array α) (work : ℕ) :
    let result := fillArrayWithWordWork value count table work
    result.1.toList = table.toList ++ List.replicate count value ∧ result.2 = work + 4 * count + 2 := by
  induction count generalizing table work with
  | zero => simp [fillArrayWithWordWork]
  | succ count ih =>
    simp only [fillArrayWithWordWork]
    obtain ⟨filled, tally⟩ := ih (table.push value) (work + 4)
    exact ⟨by simp only [filled, Array.toList_push, List.replicate_succ, List.append_assoc, List.singleton_append],
      tally.trans (by omega)⟩

/-- Reserve the flow table and initialize its signed values once. -/
def zeroFinArcFlowTableWithWordWork (n : ℕ) : FinArcFlowTable n × ℕ :=
  let size := n * n
  let result := fillArrayWithWordWork (0 : ℤ) size (Array.emptyWithCapacity size) 3
  have values := congrArg List.length (fillArrayWithWordWork_spec (0 : ℤ) size (Array.emptyWithCapacity size) 3).1
  (⟨result.1, by simpa only [show (Array.emptyWithCapacity size : Array ℤ).toList = [] from rfl,
    List.nil_append, Array.length_toList,
    List.length_replicate] using values⟩, result.2)

theorem zeroFinArcFlowTableWithWordWork_spec (n : ℕ) :
    let result := zeroFinArcFlowTableWithWordWork n
    result.1.read = (fun _ => 0) ∧ result.2 = 4 * (n * n) + 5 := by
  have filled := fillArrayWithWordWork_spec (0 : ℤ) (n*n) (Array.emptyWithCapacity (n*n)) 3
  have exactTable : (zeroFinArcFlowTableWithWordWork n).1 = zeroFinArcFlowTable n := by
    apply Subtype.ext
    apply Array.toList_inj.mp
    change (fillArrayWithWordWork (0 : ℤ) (n*n) (Array.emptyWithCapacity (n*n)) 3).1.toList = _
    simpa [zeroFinArcFlowTable] using filled.1
  exact ⟨exactTable ▸ zeroFinArcFlowTable_read n, filled.2.trans (by omega)⟩

private theorem augmentationCount_le {n : ℕ} (capacity : ArcFlow (Fin n)) (s t : Fin n)
    (supply : ℕ) (flow : ArcFlow (Fin n)) : (unitAugmentations capacity s t supply flow).2 ≤ supply := by
  induction supply generalizing flow with
  | zero => simp [unitAugmentations]
  | succ fuel ih =>
    unfold unitAugmentations
    split
    · exact Nat.zero_le _
    · exact Nat.succ_le_succ (ih _)

/-- Return the ordinary low-capacity cut with indexed signed-flow updates. -/
def findLowCapacityCutWithDenseFlowWork {n : ℕ} (capacity : ArcFlow (Fin n))
    (s t : Fin n) (supply : ℕ) : (Option (Finset (Fin n)) × ℕ) × ℕ :=
  let start := zeroFinArcFlowTableWithWordWork n
  let aug := unitAugmentationsWithDenseFlowWork capacity s t supply start.1
  let extra := start.2 + aug.2.2
  if aug.1.2 = supply then ((none, aug.2.1), extra + 4)
  else
    let residual := residualArcs capacity aug.1.1.read
    let side := reachInWithArcInspections (reverseArcs residual) s n
    ((some side.1, aug.2.1 + (n ^ 2 + n ^ 2 + side.2)), extra + 8)

theorem findLowCapacityCutWithDenseFlowWork_spec {n : ℕ} (capacity : ArcFlow (Fin n))
    (s t : Fin n) (supply : ℕ) :
    let result := findLowCapacityCutWithDenseFlowWork capacity s t supply
    result.1.1 = findLowCapacityCut capacity s t supply ∧
      result.1.2 ≤ supply * residualStepWorkBound n + (2 * n^2 + n * n^2) ∧
      result.2 ≤ 4 * (n*n) + supply * (20 * n + 10) + 18 := by
  let start := zeroFinArcFlowTableWithWordWork n
  let aug := unitAugmentationsWithDenseFlowWork capacity s t supply start.1
  let plain := unitAugmentations capacity s t supply (fun _ => 0)
  obtain ⟨starting, initWork⟩ := zeroFinArcFlowTableWithWordWork_spec n
  obtain ⟨same, search, updates⟩ := unitAugmentationsWithDenseFlowWork_spec capacity s t supply start.1
  change (aug.1.1.read, aug.1.2) = unitAugmentations capacity s t supply start.1.read at same
  rw [show start.1.read = (fun _ => 0) from starting] at same
  have flow : aug.1.1.read = plain.1 := congrArg Prod.fst same
  have count : aug.1.2 = plain.2 := congrArg Prod.snd same
  have used : aug.1.2 ≤ supply := count ▸ augmentationCount_le capacity s t supply (fun _ => 0)
  have work : start.2 + aug.2.2 ≤ 4 * (n*n) + supply * (20 * n + 10) + 10 := by
    rw [show start.2 = 4 * (n*n) + 5 from initWork]
    have updates' := updates.trans (Nat.add_le_add_right (Nat.mul_le_mul_right (20*n+10) used) 5)
    change aug.2.2 ≤ supply * (20 * n + 10) + 5 at updates'
    omega
  unfold findLowCapacityCutWithDenseFlowWork findLowCapacityCut
  simp only [← show aug = unitAugmentationsWithDenseFlowWork capacity s t supply start.1 from rfl,
    ← show start = zeroFinArcFlowTableWithWordWork n from rfl,
    ← show plain = unitAugmentations capacity s t supply (fun _ => 0) from rfl, flow, count]
  by_cases enough : plain.2 = supply
  · simp only [enough, ite_true]
    refine ⟨trivial, search.trans (Nat.le_add_right ..), ?_⟩
    omega
  · simp only [enough, ite_false]
    refine ⟨?_, ?_, by omega⟩
    · simp [reachInWithArcInspections_spec, residualReach, reaches]
    · have residual : (residualArcs capacity plain.1).card ≤ n ^ 2 := by
        simpa [pow_two, Fintype.card_prod] using card_le_univ (residualArcs capacity plain.1)
      have visits := Nat.mul_le_mul_left n residual
      simp only [reachInWithArcInspections_spec, reverseArcs_card, two_mul]
      exact Nat.add_le_add search (Nat.add_le_add_left visits _)

private theorem unitAugmentationsWithDenseFlowWork_eq {n : ℕ} (capacity : ArcFlow (Fin n))
    (s t : Fin n) (fuel : ℕ) (table : FinArcFlowTable n) :
    let result := unitAugmentationsWithDenseFlowWork capacity s t fuel table
    ((result.1.1.read, result.1.2), result.2.1) =
      unitAugmentationsWithSearchWork capacity s t fuel table.read := by
  induction fuel generalizing table with
  | zero => rfl
  | succ fuel ih =>
    let graph := residualArcs capacity table.read
    let route := routePathWithSearchWork graph s t
    cases found : route.1 with
    | none =>
      change (routePathWithSearchWork graph s t).1 = none at found
      simp only [unitAugmentationsWithDenseFlowWork, unitAugmentationsWithSearchWork,
        unitAugmentationsWithResidualWork, residualPathWithWork, residualGraphWithPairVisits,
        ← show graph = residualArcs capacity table.read from rfl, Fintype.card_fin, found]
    | some path =>
      have exactPath := (routePathWithSearchWork_spec graph s t).1
      change route.1 = routePath graph s t at exactPath
      have original := exactPath.symm.trans found
      obtain ⟨nodup, _⟩ := routedPathBound graph s t path original
      let update := augmentFinArcFlowWithWordWork table path
      have changed : update.1.read = augmentArcFlow table.read path.toFinset :=
        (augmentFinArcFlowWithWordWork_spec table path nodup).1
      let rest := unitAugmentationsWithDenseFlowWork capacity s t fuel update.1
      have tail := ih update.1
      change ((rest.1.1.read, rest.1.2), rest.2.1) =
        unitAugmentationsWithResidualWork (residualGraphWithPairVisits capacity) s t fuel update.1.read at tail
      change (routePathWithSearchWork graph s t).1 = some path at found
      simp only [unitAugmentationsWithDenseFlowWork, unitAugmentationsWithSearchWork,
        unitAugmentationsWithResidualWork, residualPathWithWork, residualGraphWithPairVisits,
        ← show graph = residualArcs capacity table.read from rfl, Fintype.card_fin, found]
      change ((rest.1.1.read, rest.1.2 + 1), n^2 + route.2.1 + route.2.2 + rest.2.1) = _
      rw [← changed, ← tail]

theorem findLowCapacityCutWithDenseFlowWork_eq {n : ℕ} (capacity : ArcFlow (Fin n))
    (s t : Fin n) (supply : ℕ) :
    (findLowCapacityCutWithDenseFlowWork capacity s t supply).1 =
      findLowCapacityCutWithSearchWork capacity s t supply := by
  let start := zeroFinArcFlowTableWithWordWork n
  let aug := unitAugmentationsWithDenseFlowWork capacity s t supply start.1
  have initial : start.1.read = (fun _ => 0) := (zeroFinArcFlowTableWithWordWork_spec n).1
  have same := unitAugmentationsWithDenseFlowWork_eq capacity s t supply start.1
  change ((aug.1.1.read, aug.1.2), aug.2.1) =
    unitAugmentationsWithResidualWork (residualGraphWithPairVisits capacity) s t supply start.1.read at same
  rw [initial] at same
  unfold findLowCapacityCutWithDenseFlowWork findLowCapacityCutWithSearchWork findLowCapacityCutWithResidualWork
  simp only [← show start = zeroFinArcFlowTableWithWordWork n from rfl,
    ← show aug = unitAugmentationsWithDenseFlowWork capacity s t supply start.1 from rfl, ← same]
  unfold residualCutSideWithWork residualGraphWithPairVisits
  simp only [Fintype.card_fin]
  split <;> simp [Nat.add_assoc]

/-- Use the same thin capacity function and selector with stored signed flow. -/
def fastThinViolationWithDenseFlowWork {n : ℕ} (G : Arcs (Fin n)) (d : Fin n × Fin n)
    (m : ℕ) (load : CutLoads (Fin n)) : (Option (Finset (Fin n)) × ℕ) × ℕ :=
  if d.1 = d.2 then ((none,0),3)
  else
    let interval := reachInterval G d
    let edges := G.filter (fun e => e.1 ∈ interval ∧ e.2 ∈ interval)
    let capacity : ArcFlow (Fin n) := fun e => if e ∈ edges then (2 : ℤ) ^ load e else 0
    let cut := findLowCapacityCutWithDenseFlowWork capacity d.1 d.2 m
    ((cut.1.1.map (· ∩ interval), cut.1.2 + (2*n*m+m)), cut.2 + 5)

theorem fastThinViolationWithDenseFlowWork_spec {n : ℕ} (G : Arcs (Fin n)) (d : Fin n × Fin n)
    (m : ℕ) (hm : m = G.card) (load : CutLoads (Fin n)) :
    let result := fastThinViolationWithDenseFlowWork G d m load
    result.1 = fastThinViolationWithSearchWork G d load ∧
      result.2 ≤ 4 * (n*n) + m * (20 * n + 10) + 23 := by
  by_cases self : d.1 = d.2
  · simp [fastThinViolationWithDenseFlowWork, fastThinViolationWithSearchWork, self]
  · let capacity := localArcCapacity G d load
    obtain ⟨_, _, work⟩ := findLowCapacityCutWithDenseFlowWork_spec capacity d.1 d.2 m
    simp only [fastThinViolationWithDenseFlowWork, fastThinViolationWithSearchWork, self, ite_false]
    change ((findLowCapacityCutWithDenseFlowWork capacity d.1 d.2 m).1.1.map (· ∩ reachInterval G d),
      (findLowCapacityCutWithDenseFlowWork capacity d.1 d.2 m).1.2 + (2*n*m+m)) = _ ∧
      (findLowCapacityCutWithDenseFlowWork capacity d.1 d.2 m).2 + 5 ≤ _
    refine ⟨?_, by omega⟩
    rw [findLowCapacityCutWithDenseFlowWork_eq, hm]
    simp only [Fintype.card_fin]
    rfl

end OnlineReachabilityPreservers
