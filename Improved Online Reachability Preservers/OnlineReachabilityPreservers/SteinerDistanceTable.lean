import OnlineReachabilityPreservers.SteinerEarlyReplay
import OnlineReachabilityPreservers.SteinerRoundingWork
import OnlineReachabilityPreservers.SteinerTemplateWork

/-! Precompute original-graph distances independently of the Steiner height forest. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V : Type*} [LinearOrder V] [Fintype V]

private def vertexPairList (V : Type*) [LinearOrder V] [Fintype V] : List (V × V) :=
  let vertices := (univ : Finset V).sort (· ≤ ·)
  vertices.flatMap fun s => vertices.map fun t => (s,t)

private theorem mem_vertexPairList (d : V × V) : d ∈ vertexPairList V := by
  unfold vertexPairList
  exact List.mem_flatMap.mpr ⟨d.1, by simp, List.mem_map.mpr ⟨d.2, by simp, rfl⟩⟩

private theorem vertexPairList_length (V : Type*) [LinearOrder V] [Fintype V] :
    (vertexPairList V).length = Fintype.card V^2 := by
  simp [vertexPairList, List.length_flatMap, pow_two]

/-- Each pair's exact hop count is stored once. The numeric field counts
the original-arc inspections needed to build this table. -/
def distanceTableWithSearchWork (G : Arcs V) : List ((V × V) × ℕ) × ℕ :=
  let evaluations := (vertexPairList V).map fun d => (d,hopsWithSearchWork G d.1 d.2)
  (evaluations.map fun row => (row.1,row.2.1), (evaluations.map fun row => row.2.2).sum)

/-- Read one stored hop value and record the number of key comparisons. -/
def readDistanceRow (rows : List ((V × V) × ℕ)) (d : V × V) : ℕ × ℕ :=
  match rows with
  | [] => (0,0)
  | row::rest =>
    if row.1 = d then (row.2,1)
    else
      let found := readDistanceRow rest d
      (found.1,found.2+1)

omit [Fintype V] in
theorem readDistanceRow_length_le (rows : List ((V × V) × ℕ)) (d : V × V) :
    (readDistanceRow rows d).2 ≤ rows.length := by
  induction rows with
  | nil => simp [readDistanceRow]
  | cons row rest ih =>
    unfold readDistanceRow
    split
    · simp
    · exact Nat.succ_le_succ ih

omit [Fintype V] in
private theorem readDistanceRow_map (pairs : List (V × V)) (dist : V × V → ℕ)
    (d : V × V) (seen : d ∈ pairs) :
    (readDistanceRow (pairs.map fun e => (e,dist e)) d).1 = dist d := by
  induction pairs with
  | nil => simp at seen
  | cons e rest ih =>
    by_cases eq : e = d
    · simp [readDistanceRow, eq]
    · have available : d ∈ rest := (List.mem_cons.mp seen).resolve_left (Ne.symm eq)
      simpa [readDistanceRow, eq] using ih available

theorem distanceTableReadWithSearchWork_spec (G : Arcs V) (d : V × V) :
    let read := readDistanceRow (distanceTableWithSearchWork G).1 d
    read.1 = hops G d.1 d.2 ∧ read.2 ≤ Fintype.card V^2 := by
  let rows := (distanceTableWithSearchWork G).1
  have length : rows.length = Fintype.card V^2 := by
    simp [rows, distanceTableWithSearchWork, vertexPairList_length]
  refine ⟨?_, (readDistanceRow_length_le rows d).trans_eq length⟩
  have rowsEq : rows = (vertexPairList V).map (fun d => (d,hops G d.1 d.2)) := by
    unfold rows distanceTableWithSearchWork
    dsimp only
    rw [List.map_map]
    apply List.map_congr_left
    intro p _
    exact congrArg (fun n => (p,n)) (hopsWithSearchWork_spec G p.1 p.2).1
  change (readDistanceRow rows d).1 = _
  rw [rowsEq]
  exact readDistanceRow_map _ _ _ (mem_vertexPairList d)

theorem distanceTableWithSearchWork_bound (G : Arcs V) :
    let n := Fintype.card V
    (distanceTableWithSearchWork G).2 ≤ n^2*((n+1)*n*G.card) := by
  let n := Fintype.card V
  let cap := (n+1)*n*G.card
  let work (d : V × V) := (hopsWithSearchWork G d.1 d.2).2
  have each (d : V × V) : work d ≤ cap := (hopsWithSearchWork_spec G d.1 d.2).2
  have sum (L : List (V × V)) : (L.map work).sum ≤ L.length * cap := by
    induction L with
    | nil => simp
    | cons e L ih =>
      simpa only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul, add_comm] using
        Nat.add_le_add (each e) ih
  unfold distanceTableWithSearchWork
  simp only [List.map_map]
  rw [← vertexPairList_length V]
  exact sum _

/-- The one-out-of-range hop count denotes an unreachable pair. -/
theorem hops_le_vertices_iff (G : Arcs V) (s t : V) :
    hops G s t ≤ Fintype.card V ↔ Reach G s t := by
  refine ⟨?_, fun reach => (hops_spec reach).1⟩
  intro valid
  let candidates := (range (Fintype.card V+1)).filter (fun d => s ∈ reachIn G t d)
  change (least? candidates).getD (Fintype.card V+1) ≤ Fintype.card V at valid
  cases selection : least? candidates with
  | none => simp [selection] at valid
  | some k =>
    have found := least?_mem selection
    change k ∈ (range (Fintype.card V+1)).filter (fun d => s ∈ reachIn G t d) at found
    exact reachIn_sound (mem_filter.mp found).2

private def heightTreeFromDistances (dist : V × V → ℕ) (root : V) (height : ℕ) :
    Arcs (HeightNode V height) :=
  (univ.filter fun node : HeightNode V height => node.val ≠ [] ∧
    (root::node.val).IsChain (fun a b => dist (b,a) ≤ Fintype.card V)).image
    (fun node => (node,heightParent node))

private theorem heightTreeFromDistances_eq (G : Arcs V) (dist : V × V → ℕ)
    (isReach : ∀ a b, dist (a,b) ≤ Fintype.card V ↔ Reach G a b) (root : V) (height : ℕ) :
    heightTreeFromDistances dist root height = inwardHeightTree G root height := by
  have equal : (univ : Finset (HeightNode V height)).filter (fun node => node.val ≠ [] ∧
      (root::node.val).IsChain (fun a b => dist (b,a) ≤ Fintype.card V)) =
      univ.filter (fun node => node.val ≠ [] ∧ heightHistoryValid G root node) := by
    ext u
    rw [mem_filter, mem_filter]
    simp only [mem_univ, true_and]
    unfold heightHistoryValid
    exact and_congr_right fun _ => List.IsChain.iff (fun a b => (isReach b a).trans mem_reaches.symm)
  exact congrArg (fun S => S.image (fun node => (node,heightParent node))) equal

/-- Use stored distances in both orientations to build the same paired
forest without invoking reachability on its history candidates. -/
def heightForestFromDistances (dist : V × V → ℕ) (height : ℕ) : Arcs (HeightForestVertex V height) :=
  univ.biUnion fun r => joinHeightCopies r (heightTreeFromDistances dist r height)
    (heightTreeFromDistances (fun d => dist d.swap) r height)

theorem heightForestFromDistances_eq (G : Arcs V) (dist : V × V → ℕ)
    (values : ∀ d : V × V, dist d = hops G d.1 d.2) (height : ℕ) :
    heightForestFromDistances dist height = heightForest G height := by
  have yes (a b : V) : dist (a,b) ≤ Fintype.card V ↔ Reach G a b :=
    (values (a,b)) ▸ hops_le_vertices_iff G a b
  have rev (a b : V) : dist ((a,b) : V × V).swap ≤ Fintype.card V ↔ Reach (reverseArcs G) a b :=
    (yes b a).trans reach_reverseArcs.symm
  unfold heightForestFromDistances heightForest
  apply Finset.biUnion_congr rfl
  intro root _
  rw [heightTreeFromDistances_eq G dist yes root height,
    heightTreeFromDistances_eq (reverseArcs G) (fun d => dist d.swap) rev root height]

private def historyDistanceRead (lookup : V × V → ℕ × ℕ) (a b : V) : Bool × ℕ :=
  let entry := lookup (b,a)
  (decide (entry.1 ≤ Fintype.card V),entry.2)

theorem heightForestWithDistanceTableWork_spec (G : Arcs V) (height : ℕ) :
    let rows := (distanceTableWithSearchWork G).1
    let read := readDistanceRow rows
    let out := heightForestWithDistanceWork (historyDistanceRead read)
      (historyDistanceRead (fun d => read d.swap)) height
    out.1 = heightForest G height ∧
      out.2 ≤ Fintype.card V*(2*Fintype.card (HeightNode V height)*height*(Fintype.card V^2)) := by
  let read := readDistanceRow (distanceTableWithSearchWork G).1
  have value (a b : V) : (read (a,b)).1 ≤ Fintype.card V ↔ Reach G a b := by
    change (readDistanceRow (distanceTableWithSearchWork G).1 (a,b)).1 ≤ _ ↔ _
    rw [(distanceTableReadWithSearchWork_spec G (a,b)).1, hops_le_vertices_iff]
  have left (a b : V) : (historyDistanceRead read a b).1 = true ↔ Reach G b a := by
    simpa only [historyDistanceRead,decide_eq_true_eq] using value b a
  have right (a b : V) : (historyDistanceRead (fun d => read d.swap) a b).1 = true ↔
      Reach (reverseArcs G) b a := by
    change decide ((read (a,b)).1 ≤ Fintype.card V) = true ↔ Reach (reverseArcs G) b a
    rw [decide_eq_true_eq,reach_reverseArcs]
    exact value a b
  exact heightForestWithDistanceWork_spec G _ _ left right _
    (fun a b => (distanceTableReadWithSearchWork_spec G (b,a)).2)
    (fun a b => (distanceTableReadWithSearchWork_spec G (a,b)).2) height

section ForestWeights

variable {height : ℕ}

local instance : DecidableEq (ForestNetworkVertex V height) :=
  (inferInstance : LinearOrder (ForestNetworkVertex V height)).toDecidableEq

/-- Read the original hop weight of a link using its two original labels. -/
def forestWeightFromDistances (dist : V × V → ℕ)
    (e : HeightForestVertex V height × HeightForestVertex V height) : ℕ :=
  dist (heightForestLabel e.1,heightForestLabel e.2)

private theorem forestWeightFromDistances_eq (G : Arcs V) (dist : V × V → ℕ)
    (values : ∀ d : V × V, dist d = hops G d.1 d.2) :
    forestWeightFromDistances (height := height) dist = heightForestWeight G :=
  funext fun e => values (heightForestLabel e.1,heightForestLabel e.2)

private def pricedForestFromWeights (links : Arcs (HeightForestVertex V height))
    (weights : HeightForestVertex V height × HeightForestVertex V height → ℕ) :
    Arcs (ForestNetworkVertex V height) :=
  (links.filter fun e => 0 < weights e).map (forestNetworkCopy.prodMap forestNetworkCopy)

private def freeForestFromWeights (links : Arcs (HeightForestVertex V height))
    (weights : HeightForestVertex V height × HeightForestVertex V height → ℕ) :
    Arcs (ForestNetworkVertex V height) :=
  (links.filter fun e => weights e = 0).map (forestNetworkCopy.prodMap forestNetworkCopy)

private def networkWeightFromForestWeights
    (weights : HeightForestVertex V height × HeightForestVertex V height → ℕ)
    (e : ForestNetworkVertex V height × ForestNetworkVertex V height) : ℕ :=
  weights ((ofLex e.1).2,(ofLex e.2).2)

private def requestOnFreeForest (free : Arcs (ForestNetworkVertex V height)) (d : V × V) :
    WeightedNetworkDemand (ForestNetworkVertex V height) :=
  ⟨free ∪ forestNetworkEntries d.1 ∪ forestNetworkExits d.2,
    forestNetworkSource d.1,forestNetworkSink d.2⟩

private def forestFractionalWithPreparedInputs (priced free : Arcs (ForestNetworkVertex V height))
    (weight : ForestNetworkVertex V height × ForestNetworkVertex V height → ℕ)
    (scale fuel : ℕ) (D : List (V × V)) :
    (((ForestNetworkVertex V height × ForestNetworkVertex V height) → ℕ) ×
      List (Arcs (ForestNetworkVertex V height))) × ℕ :=
  weightedNetworkRunAtScaleWithSearchWork priced weight scale fuel
    (D.map (requestOnFreeForest free)) (fun _ => 0)

/-- Use one paired template and its stored original-graph hop values in all
weighted separators. The graph searches have the ordinary flow outputs. -/
def forestFractionalFromWeightsWithSearchWork
    (links : Arcs (HeightForestVertex V height))
    (weight : HeightForestVertex V height × HeightForestVertex V height → ℕ) :
    List (V × V) →
    (((ForestNetworkVertex V height × ForestNetworkVertex V height) → ℕ) ×
      List (Arcs (ForestNetworkVertex V height))) × ℕ :=
  let priced := pricedForestFromWeights links weight
  let free := freeForestFromWeights links weight
  let liftedWeight := networkWeightFromForestWeights weight
  forestFractionalWithPreparedInputs priced free liftedWeight
    (weightedCoverScale priced liftedWeight) (weightedCoverFuel priced liftedWeight)

theorem forestFractionalFromWeightsWithSearchWork_eq (G : Arcs V) (dist : V × V → ℕ)
    (values : ∀ d : V × V, dist d = hops G d.1 d.2) (height : ℕ) (D : List (V × V)) :
    forestFractionalFromWeightsWithSearchWork (heightForestFromDistances dist height)
      (forestWeightFromDistances dist) D = forestFractionalRunWithSearchWork G height D := by
  rw [heightForestFromDistances_eq G dist values height, forestWeightFromDistances_eq G dist values]
  rfl

theorem roundedForestTrialsFromWeights_eq (G : Arcs V) (dist : V × V → ℕ)
    (values : ∀ d : V × V, dist d = hops G d.1 d.2)
    (charges : ForestNetworkVertex V height × ForestNetworkVertex V height → ℕ) (scale trials : ℕ)
    (sample : ForestTrialArray V height scale trials) :
    roundedForestTrialsFromWeights (heightForestFromDistances dist height) (forestWeightFromDistances dist)
      charges scale trials sample = roundedForestTrials G charges scale trials sample := by
  rw [heightForestFromDistances_eq G dist values height, forestWeightFromDistances_eq G dist values]
  rfl

/-- Read a forest link's original hop weight together with the table work. -/
def forestWeightWithDistanceWork (read : V × V → ℕ × ℕ)
    (e : HeightForestVertex V height × HeightForestVertex V height) : ℕ × ℕ :=
  read (heightForestLabel e.1,heightForestLabel e.2)

/-- The rounded trial union for a prepared template and stored metric is exact.
Count only key comparisons made by these weight reads. -/
theorem roundedForestTrialsWithDistanceTable_spec (G : Arcs V)
    (links : Arcs (HeightForestVertex V height)) (same : links = heightForest G height)
    (charges : ForestNetworkVertex V height × ForestNetworkVertex V height → ℕ) (scale trials : ℕ)
    (sample : ForestTrialArray V height scale trials) :
    let read := readDistanceRow (distanceTableWithSearchWork G).1
    let out := roundedForestTrialsWithWork links (forestWeightWithDistanceWork read) charges scale trials sample
    out.1 = roundedForestTrials G charges scale trials sample ∧
      out.2 ≤ trials*(links.card*((1+(scale.log2+1)*(2*(height+1)^2))*Fintype.card V^2)) := by
  let read := readDistanceRow (distanceTableWithSearchWork G).1
  let weight := forestWeightWithDistanceWork (height := height) read
  have scanBound (e : HeightForestVertex V height × HeightForestVertex V height) :
      (weight e).2 ≤ Fintype.card V^2 :=
    (distanceTableReadWithSearchWork_spec G _).2
  have correct : (fun e => (weight e).1) = heightForestWeight G :=
    funext fun e => (distanceTableReadWithSearchWork_spec G (heightForestLabel e.1,heightForestLabel e.2)).1
  obtain ⟨graph, work⟩ := roundedForestTrialsWithWork_spec links weight charges scale trials _ scanBound sample
  refine ⟨graph.trans ?_,work⟩
  rw [correct, same]
  rfl

private def preparedScaleAndFuel (priced : Arcs (ForestNetworkVertex V height))
    (weight : ForestNetworkVertex V height × ForestNetworkVertex V height → ℕ) : ℕ × ℕ :=
  let total := ∑ e ∈ priced, weight e
  let scale := max 1 total
  (scale,(scale.log2+1)*total+1)

private theorem forestScaleFromWeights_eq (G : Arcs V) (dist : V × V → ℕ)
    (values : ∀ d : V × V, dist d = hops G d.1 d.2) (height : ℕ)
    (links : Arcs (HeightForestVertex V height)) (correct : links = heightForestFromDistances dist height) :
    (preparedScaleAndFuel (pricedForestFromWeights links (forestWeightFromDistances dist))
      (networkWeightFromForestWeights (forestWeightFromDistances dist))).1 =
        forestScale G height := by
  rw [correct,heightForestFromDistances_eq G dist values height, forestWeightFromDistances_eq G dist values]
  rfl

private theorem roundedTrials_cast_scale (G : Arcs V) {scale : ℕ}
    (same : scale = forestScale G height) (sample : EarlyRoundSample G height)
    (charge : ForestNetworkVertex V height × ForestNetworkVertex V height → ℕ) :
    roundedForestTrials G charge scale (earlyTrialCount V height)
      (cast (congrArg (fun k => ForestTrialArray V height k (earlyTrialCount V height)) same.symm) sample) =
      roundedForestTrials G charge (forestScale G height) (earlyTrialCount V height) sample := by
  subst scale
  rfl

private def earlyMetricWithPreparedInputs (links : Arcs (HeightForestVertex V height))
    (weight : HeightForestVertex V height × HeightForestVertex V height → ℕ)
    (priced free : Arcs (ForestNetworkVertex V height))
    (networkWeight : ForestNetworkVertex V height × ForestNetworkVertex V height → ℕ)
    (scale fuel : ℕ) (seed : ForestTrialArray V height scale (earlyTrialCount V height))
    (P : List (V × V)) : Arcs (HeightForestVertex V height) × ℕ :=
  let out := forestFractionalWithPreparedInputs priced free networkWeight scale fuel P
  (roundedForestTrialsFromWeights links weight out.1.1 scale (earlyTrialCount V height) seed,out.2)

private theorem earlyMetricWithPreparedInputs_eq (G : Arcs V) (height : ℕ) (dist : V × V → ℕ)
    (values : ∀ d : V × V, dist d = hops G d.1 d.2)
    (links : Arcs (HeightForestVertex V height)) (correct : links = heightForestFromDistances dist height)
    (sample : EarlyRoundSample G height) :
    let weight := forestWeightFromDistances dist
    let priced := pricedForestFromWeights links weight
    let free := freeForestFromWeights links weight
    let networkWeight := networkWeightFromForestWeights weight
    let sizes := preparedScaleAndFuel priced networkWeight
    let scale := sizes.1
    let fuel := sizes.2
    let seed : ForestTrialArray V height scale (earlyTrialCount V height) :=
      cast (congrArg (fun k => ForestTrialArray V height k (earlyTrialCount V height))
        (forestScaleFromWeights_eq G dist values height links correct).symm) sample
    earlyMetricWithPreparedInputs links weight priced free networkWeight scale fuel seed =
      earlyMetricWithSearchWork G height sample := by
  subst links
  funext P
  let links := heightForestFromDistances dist height
  let weight := forestWeightFromDistances (height := height) dist
  let priced := pricedForestFromWeights links weight
  let free := freeForestFromWeights links weight
  let networkWeight := networkWeightFromForestWeights weight
  let sizes := preparedScaleAndFuel priced networkWeight
  have fraction : forestFractionalWithPreparedInputs priced free networkWeight
      sizes.1 sizes.2 P =
      forestFractionalRunWithSearchWork G height P :=
    forestFractionalFromWeightsWithSearchWork_eq G dist values height P
  dsimp only [earlyMetricWithPreparedInputs, earlyMetricWithSearchWork]
  rw [fraction,
    roundedForestTrialsFromWeights_eq G dist values,
    roundedTrials_cast_scale G (forestScaleFromWeights_eq G dist values height links rfl)]

end ForestWeights

/-- Prepare one early evaluator. Report distance-table arc inspections and
the key comparisons made to construct the paired template separately. -/
def prepareEarlyDistanceTableWithTemplateWork (G : Arcs V) (height : ℕ) (sample : EarlyRoundSample G height) :
    (List (V × V) → Arcs V × ℕ) × ℕ × ℕ :=
  let table := distanceTableWithSearchWork G
  let query := readDistanceRow table.1
  let dist := fun d => (query d).1
  let known : ∀ d : V × V, dist d = hops G d.1 d.2 :=
    fun d => (distanceTableReadWithSearchWork_spec G d).1
  let template := heightForestWithDistanceWork (historyDistanceRead query)
    (historyDistanceRead (fun d => query d.swap)) height
  let correct : template.1 = heightForestFromDistances dist height :=
    (heightForestWithDistanceTableWork_spec G height).1.trans (heightForestFromDistances_eq G dist known height).symm
  let links := template.1
  let weight := forestWeightFromDistances dist
  let priced := pricedForestFromWeights links weight
  let free := freeForestFromWeights links weight
  let networkWeight := networkWeightFromForestWeights weight
  let sizes := preparedScaleAndFuel priced networkWeight
  let scale := sizes.1
  let fuel := sizes.2
  let seed : ForestTrialArray V height scale (earlyTrialCount V height) :=
    cast (congrArg (fun k => ForestTrialArray V height k (earlyTrialCount V height))
      (forestScaleFromWeights_eq G dist known height links correct).symm) sample
  let metric := earlyMetricWithPreparedInputs links weight priced free networkWeight scale fuel seed
  (earlyRoundedGraphWithSearchWorkFromMetric G height metric,table.2,template.2)

theorem prepareEarlyDistanceTableWithTemplateWork_spec (G : Arcs V) (height : ℕ)
    (sample : EarlyRoundSample G height) :
    let out := prepareEarlyDistanceTableWithTemplateWork G height sample
    out.1 = earlyRoundedGraphWithSearchWork G height sample ∧
      out.2.1 = (distanceTableWithSearchWork G).2 ∧
      out.2.2 ≤ Fintype.card V*(2*Fintype.card (HeightNode V height)*height*(Fintype.card V^2)) := by
  let query := readDistanceRow (distanceTableWithSearchWork G).1
  let dist := fun d => (query d).1
  have known (d : V × V) : dist d = hops G d.1 d.2 :=
    (distanceTableReadWithSearchWork_spec G d).1
  let template := heightForestWithDistanceWork (historyDistanceRead query)
    (historyDistanceRead (fun d => query d.swap)) height
  have spec := heightForestWithDistanceTableWork_spec G height
  have correct : template.1 = heightForestFromDistances dist height :=
    spec.1.trans (heightForestFromDistances_eq G dist known height).symm
  refine ⟨?_,rfl,spec.2⟩
  exact congrArg (earlyRoundedGraphWithSearchWorkFromMetric G height)
    (earlyMetricWithPreparedInputs_eq G height dist known template.1 correct sample)

/-- The measured graph searches, with the same distance-table preparation. -/
def prepareEarlyDistanceTable (G : Arcs V) (height : ℕ) (sample : EarlyRoundSample G height) :
    (List (V × V) → Arcs V × ℕ) × ℕ :=
  let prepared := prepareEarlyDistanceTableWithTemplateWork G height sample
  (prepared.1,prepared.2.1)

theorem prepareEarlyDistanceTable_eq (G : Arcs V) (height : ℕ) (sample : EarlyRoundSample G height) :
    prepareEarlyDistanceTable G height sample =
      (earlyRoundedGraphWithSearchWork G height sample,(distanceTableWithSearchWork G).2) := by
  have out := prepareEarlyDistanceTableWithTemplateWork_spec G height sample
  exact Prod.ext out.1 out.2.1

/-- Construct original distances once before building the height forest.
The separator and rounding use stored values for original metric queries. -/
def earlyRoundedGraphWithDistanceTable (G : Arcs V) (height : ℕ) (sample : EarlyRoundSample G height)
    (D : List (V × V)) : Arcs V × ℕ :=
  let prepared := prepareEarlyDistanceTable G height sample
  let out := prepared.1 D
  (out.1,out.2+prepared.2)

theorem earlyRoundedGraphWithDistanceTable_eq (G : Arcs V) (height : ℕ)
    (sample : EarlyRoundSample G height) (D : List (V × V)) :
    let ordinary := earlyRoundedGraphWithSearchWork G height sample D
    earlyRoundedGraphWithDistanceTable G height sample D = (ordinary.1,ordinary.2+(distanceTableWithSearchWork G).2) := by
  simp only [earlyRoundedGraphWithDistanceTable, prepareEarlyDistanceTable_eq]

theorem earlyRoundedGraphWithDistanceTable_spec (G : Arcs V) (height : ℕ)
    (sample : EarlyRoundSample G height) (D : List (V × V)) :
    let n := Fintype.card V
    let F := Fintype.card (HeightForestVertex V height)
    let N := Fintype.card (ForestNetworkVertex V height)
    let out := earlyRoundedGraphWithDistanceTable G height sample D
    out.1 = earlyRoundedGraph G height D sample ∧
      out.2 ≤ earlySearchWorkBound n G.card F N D.length+n^2*((n+1)*n*G.card) := by
  rw [earlyRoundedGraphWithDistanceTable_eq]
  have ordinary := earlyRoundedGraphWithSearchWork_spec G height sample D
  exact ⟨ordinary.1,Nat.add_le_add ordinary.2 (distanceTableWithSearchWork_bound G)⟩

end OnlineReachabilityPreservers
