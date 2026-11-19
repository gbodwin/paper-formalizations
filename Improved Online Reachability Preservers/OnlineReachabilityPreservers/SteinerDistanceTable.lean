import OnlineReachabilityPreservers.SteinerCapacityWork
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

private def storedForestWeightRow
    (read : HeightForestVertex V height × HeightForestVertex V height → ℕ × ℕ) :
    (HeightForestVertex V height × HeightForestVertex V height) ↪
      (HeightForestVertex V height × HeightForestVertex V height) × (ℕ × ℕ) :=
  ⟨fun e => (e,read e),fun _ _ same => congrArg Prod.fst same⟩

private def selectedPreparedForestArcs
    (rows : Finset ((HeightForestVertex V height × HeightForestVertex V height) × (ℕ × ℕ)))
    (select : ℕ → Prop) [DecidablePred select] : Arcs (ForestNetworkVertex V height) :=
  (rows.filter fun r => select r.2.1).image fun r => forestNetworkCopy.prodMap forestNetworkCopy r.1

omit [Fintype V] in
private theorem selectedPreparedForestArcs_eq (links : Arcs (HeightForestVertex V height))
    (read : HeightForestVertex V height × HeightForestVertex V height → ℕ × ℕ)
    (select : ℕ → Prop) [DecidablePred select] :
    selectedPreparedForestArcs (links.map (storedForestWeightRow read)) select =
      (links.filter (fun e => select (read e).1)).map (forestNetworkCopy.prodMap forestNetworkCopy) := by
  let row := storedForestWeightRow read
  let lift := (forestNetworkCopy (V := V) (height := height)).prodMap (forestNetworkCopy (V := V) (height := height))
  ext f
  change f ∈ ((links.map row).filter fun r => select r.2.1).image (fun r => lift r.1) ↔
    f ∈ (links.filter fun e => select (read e).1).map lift
  constructor
  · intro inside
    obtain ⟨r,found,rfl⟩ := mem_image.mp inside
    obtain ⟨mapped,chosen⟩ := mem_filter.mp found
    obtain ⟨e,present,rfl⟩ := mem_map.mp mapped
    exact mem_map_of_mem _ (mem_filter.mpr ⟨present,chosen⟩)
  · intro inside
    obtain ⟨e,found,rfl⟩ := mem_map.mp inside
    obtain ⟨present,chosen⟩ := mem_filter.mp found
    exact mem_image.mpr ⟨row e, mem_filter.mpr ⟨mem_map_of_mem _ present,chosen⟩,rfl⟩

/-- Evaluate each link once to build both weighted classes and their fixed
scale and fuel. The extra charge counts the original weight reads. -/
private def prepareForestWeights (links : Arcs (HeightForestVertex V height))
    (read : HeightForestVertex V height × HeightForestVertex V height → ℕ × ℕ) :
    (Arcs (ForestNetworkVertex V height) × Arcs (ForestNetworkVertex V height)) × (ℕ × ℕ) × ℕ :=
  let rows := links.map (storedForestWeightRow read)
  let priced := selectedPreparedForestArcs rows (fun w => 0 < w)
  let free := selectedPreparedForestArcs rows (fun w => w = 0)
  let total := ∑ r ∈ rows, r.2.1
  let scale := max 1 total
  ((priced,free),(scale,(scale.log2+1)*total+1),∑ r ∈ rows, r.2.2)

omit [Fintype V] in
private theorem prepareForestWeights_spec (links : Arcs (HeightForestVertex V height))
    (read : HeightForestVertex V height × HeightForestVertex V height → ℕ × ℕ)
    (B : ℕ) (each : ∀ e, (read e).2 ≤ B) :
    let weight := fun e => (read e).1
    let priced := pricedForestFromWeights links weight
    let out := prepareForestWeights links read
    out.1.1 = priced ∧ out.1.2 = freeForestFromWeights links weight ∧
      out.2.1 = preparedScaleAndFuel priced (networkWeightFromForestWeights weight) ∧
      out.2.2 ≤ links.card*B := by
  let row := storedForestWeightRow read
  let rows := links.map row
  let weight := fun e => (read e).1
  let paid := links.filter fun e => 0 < weight e
  let lift := (forestNetworkCopy (V := V) (height := height)).prodMap (forestNetworkCopy (V := V) (height := height))
  have total : (∑ r ∈ rows, r.2.1) = ∑ e ∈ paid.map lift, networkWeightFromForestWeights weight e := by
    change (∑ r ∈ links.map row, r.2.1) = _
    rw [sum_map,sum_map]
    change (∑ e ∈ links, weight e) = ∑ e ∈ paid, weight e
    rw [show paid = links.filter (fun e => 0 < weight e) from rfl,sum_filter]
    apply sum_congr rfl
    intro e _
    by_cases valid : 0 < weight e
    · simp only [valid,ite_true]
    · simp [Nat.eq_zero_of_not_pos valid]
  refine ⟨selectedPreparedForestArcs_eq links read (fun w => 0 < w),
    selectedPreparedForestArcs_eq links read (fun w => w = 0),?_,?_⟩
  · dsimp only [prepareForestWeights, preparedScaleAndFuel]
    rw [total]
    rfl
  · change (∑ r ∈ links.map row, r.2.2) ≤ _
    rw [sum_map]
    calc
      _ ≤ ∑ _ ∈ links, B := sum_le_sum (fun e _ => each e)
      _ = _ := by simp

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

private def earlyMetricWithPreparedRoundingWork (links : Arcs (HeightForestVertex V height))
    (read : V × V → ℕ × ℕ) (priced free : Arcs (ForestNetworkVertex V height))
    (networkWeight : ForestNetworkVertex V height × ForestNetworkVertex V height → ℕ)
    (scale fuel : ℕ) (seed : ForestTrialArray V height scale (earlyTrialCount V height))
    (P : List (V × V)) : Arcs (HeightForestVertex V height) × ℕ :=
  let out := forestFractionalWithPreparedInputs priced free networkWeight scale fuel P
  let rounded := roundedForestTrialsWithWork links (forestWeightWithDistanceWork read) out.1.1 scale
    (earlyTrialCount V height) seed
  (rounded.1,out.2+rounded.2)

private def networkWeightWithDistanceWork (read : V × V → ℕ × ℕ)
    (e : ForestNetworkVertex V height × ForestNetworkVertex V height) : ℕ × ℕ :=
  forestWeightWithDistanceWork read ((ofLex e.1).2,(ofLex e.2).2)

private def earlyMetricWithPreparedCapacityWork (links : Arcs (HeightForestVertex V height))
    (read : V × V → ℕ × ℕ) (priced free : Arcs (ForestNetworkVertex V height))
    (scale fuel : ℕ) (seed : ForestTrialArray V height scale (earlyTrialCount V height))
    (P : List (V × V)) : Arcs (HeightForestVertex V height) × ℕ :=
  let out := weightedNetworkRunAtScaleWithCapacityWork priced (networkWeightWithDistanceWork read)
    scale fuel (P.map (requestOnFreeForest free)) (fun _ => 0)
  let rounded := roundedForestTrialsWithWork links (forestWeightWithDistanceWork read) out.1.1 scale
    (earlyTrialCount V height) seed
  (rounded.1,out.2+rounded.2)

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

private inductive EarlyWork
  | search
  | rounding
  | capacity

private def prepareEarlyDistanceTableBy (G : Arcs V) (height : ℕ) (sample : EarlyRoundSample G height)
    (work : EarlyWork) : (List (V × V) → Arcs V × ℕ) × ℕ × ℕ :=
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
  let metric := match work with
    | .search => earlyMetricWithPreparedInputs links weight priced free networkWeight scale fuel seed
    | .rounding => earlyMetricWithPreparedRoundingWork links query priced free networkWeight scale fuel seed
    | .capacity => earlyMetricWithPreparedCapacityWork links query priced free scale fuel seed
  (earlyRoundedGraphWithSearchWorkFromMetric G height metric,table.2,template.2)

/-- Prepare one early evaluator. Report distance-table arc inspections and
key comparisons constructing the paired template separately. -/
def prepareEarlyDistanceTableWithTemplateWork (G : Arcs V) (height : ℕ) (sample : EarlyRoundSample G height) :
    (List (V × V) → Arcs V × ℕ) × ℕ × ℕ :=
  prepareEarlyDistanceTableBy G height sample .search

/-- Use the same preparation and also charge rounding weight reads in the
early prefix evaluator. -/
def prepareEarlyDistanceTableWithRoundingWork (G : Arcs V) (height : ℕ) (sample : EarlyRoundSample G height) :
    (List (V × V) → Arcs V × ℕ) × ℕ × ℕ :=
  prepareEarlyDistanceTableBy G height sample .rounding

/-- Add capacity table construction and its original weight reads to the rounding work. -/
def prepareEarlyDistanceTableWithCapacityWork (G : Arcs V) (height : ℕ) (sample : EarlyRoundSample G height) :
    (List (V × V) → Arcs V × ℕ) × ℕ × ℕ :=
  prepareEarlyDistanceTableBy G height sample .capacity

private abbrev EarlyWeightPlan (V : Type*) (height : ℕ) :=
  (Arcs (ForestNetworkVertex V height) × Arcs (ForestNetworkVertex V height)) × (ℕ × ℕ)

private def earlyCapacityMetricFromPlan (G : Arcs V) (height : ℕ) (sample : EarlyRoundSample G height)
    (link : Arcs (HeightForestVertex V height)) (read : V × V → ℕ × ℕ)
    (plan : EarlyWeightPlan V height) (scale : plan.2.1 = forestScale G height) :
    List (V × V) → Arcs (HeightForestVertex V height) × ℕ :=
  let seed : ForestTrialArray V height plan.2.1 (earlyTrialCount V height) :=
    cast (congrArg (fun k => ForestTrialArray V height k (earlyTrialCount V height)) scale.symm) sample
  earlyMetricWithPreparedCapacityWork link read plan.1.1 plan.1.2 plan.2.1 plan.2.2 seed

private theorem earlyCapacityMetricFromPlan_congr (G : Arcs V) (height : ℕ) (sample : EarlyRoundSample G height)
    (link : Arcs (HeightForestVertex V height)) (read : V × V → ℕ × ℕ)
    (a b : EarlyWeightPlan V height) (same : a = b)
    (aScale : a.2.1 = forestScale G height) (bScale : b.2.1 = forestScale G height) :
    earlyCapacityMetricFromPlan G height sample link read a aScale =
      earlyCapacityMetricFromPlan G height sample link read b bScale := by
  subst b
  rfl

/-- Also meter preparation of the weighted link classes, scale, and fuel.
The table, forest, and weighted plan are constructed once. -/
def prepareEarlyDistanceTableWithWeightWork (G : Arcs V) (height : ℕ) (sample : EarlyRoundSample G height) :
    (List (V × V) → Arcs V × ℕ) × ℕ × ℕ × ℕ :=
  let table := distanceTableWithSearchWork G
  let query := readDistanceRow table.1
  let dist := fun d => (query d).1
  let known : ∀ d : V × V, dist d = hops G d.1 d.2 :=
    fun d => (distanceTableReadWithSearchWork_spec G d).1
  let template := heightForestWithDistanceWork (historyDistanceRead query)
    (historyDistanceRead (fun d => query d.swap)) height
  let links := template.1
  let correct : links = heightForestFromDistances dist height :=
    (heightForestWithDistanceTableWork_spec G height).1.trans (heightForestFromDistances_eq G dist known height).symm
  let priced := prepareForestWeights links (forestWeightWithDistanceWork query)
  let spec := prepareForestWeights_spec links (forestWeightWithDistanceWork query) (Fintype.card V^2)
    (fun _ => (distanceTableReadWithSearchWork_spec G _).2)
  let scale : priced.2.1.1 = forestScale G height :=
    (congrArg Prod.fst spec.2.2.1).trans (forestScaleFromWeights_eq G dist known height links correct)
  let metric := earlyCapacityMetricFromPlan G height sample links query (priced.1,priced.2.1) scale
  (earlyRoundedGraphWithSearchWorkFromMetric G height metric,table.2,template.2,priced.2.2)

theorem prepareEarlyDistanceTableWithWeightWork_spec (G : Arcs V) (height : ℕ) (sample : EarlyRoundSample G height) :
    let out := prepareEarlyDistanceTableWithWeightWork G height sample
    let old := prepareEarlyDistanceTableWithCapacityWork G height sample
    out.1 = old.1 ∧ out.2.1 = old.2.1 ∧ out.2.2.1 = old.2.2 ∧
      out.2.2.2 ≤ Fintype.card (HeightForestVertex V height)^2 * Fintype.card V^2 := by
  let query := readDistanceRow (distanceTableWithSearchWork G).1
  let dist := fun d => (query d).1
  have known (d : V × V) : dist d = hops G d.1 d.2 :=
    (distanceTableReadWithSearchWork_spec G d).1
  let template := heightForestWithDistanceWork (historyDistanceRead query)
    (historyDistanceRead (fun d => query d.swap)) height
  let links := template.1
  have correct : links = heightForestFromDistances dist height :=
    (heightForestWithDistanceTableWork_spec G height).1.trans (heightForestFromDistances_eq G dist known height).symm
  let counted := prepareForestWeights links (forestWeightWithDistanceWork query)
  let weight := forestWeightFromDistances (height := height) dist
  let priced := pricedForestFromWeights links weight
  let free := freeForestFromWeights links weight
  let setup := preparedScaleAndFuel priced (networkWeightFromForestWeights weight)
  have scaleEq : setup.1 = forestScale G height := forestScaleFromWeights_eq G dist known height links correct
  obtain ⟨paid,unpaid,sizes,compares⟩ := prepareForestWeights_spec links (forestWeightWithDistanceWork query)
    (Fintype.card V^2) (fun _ => (distanceTableReadWithSearchWork_spec G _).2)
  have planEq : (counted.1,counted.2.1) = ((priced,free),setup) := Prod.ext (Prod.ext paid unpaid) sizes
  have scale : counted.2.1.1 = forestScale G height := (congrArg Prod.fst sizes).trans scaleEq
  have linksBound : links.card ≤ Fintype.card (HeightForestVertex V height)^2 := by
    simpa only [Fintype.card_prod, pow_two] using card_le_univ links
  refine ⟨?_,rfl,rfl,compares.trans (Nat.mul_le_mul_right _ linksBound)⟩
  exact congrArg (earlyRoundedGraphWithSearchWorkFromMetric G height)
    (earlyCapacityMetricFromPlan_congr G height sample links query _ _ planEq scale scaleEq)

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

/-- One rounded fractional state makes polynomially many key comparisons
for each fixed height. -/
def roundingComparisonPolynomial (n height : ℕ) : ℕ :=
  let F := (n*2)*((height+1)*n^height)
  let S := 1+n*F^2
  let trials := 16*(height+1)^2*(n+1)
  trials*(F^2*((1+(S+1)*(2*(height+1)^2))*n^2))

private theorem roundingComparisonBound_le (G : Arcs V) (height : ℕ)
    (links : Arcs (HeightForestVertex V height)) (scale : ℕ) (scaleEq : scale = forestScale G height) :
    earlyTrialCount V height*(links.card*((1+(scale.log2+1)*(2*(height+1)^2))*Fintype.card V^2)) ≤
      roundingComparisonPolynomial (Fintype.card V) height := by
  let n := Fintype.card V
  let F := (n*2)*((height+1)*n^height)
  have forest : Fintype.card (HeightForestVertex V height) ≤ F := by
    cases isEmpty_or_nonempty V with
    | inl empty => simp [HeightForestVertex]
    | inr ne => exact heightForestVertex_card_le V height
  have linksBound : links.card ≤ F^2 := by
    have raw := card_le_univ links
    rw [Fintype.card_prod, ← pow_two] at raw
    exact raw.trans (Nat.pow_le_pow_left forest _)
  have scaleBound : scale.log2 ≤ 1+n*F^2 := by
    apply (Nat.log2_le_self scale).trans
    rw [scaleEq]
    apply (forestNetworkScale_le G height).trans
    refine max_le (Nat.le_add_right _ _) (le_trans ?_ (Nat.le_add_left _ _))
    gcongr
  unfold roundingComparisonPolynomial earlyTrialCount
  dsimp only
  gcongr
  exact Nat.log2_le_self _

/-- Including the rounding reads changes only the charge, by at most one
rounding budget per evaluated early prefix. The shared preparation is unchanged. -/
theorem prepareEarlyDistanceTableWithRoundingWork_spec (G : Arcs V) (height : ℕ)
    (sample : EarlyRoundSample G height) :
    let plain := prepareEarlyDistanceTableWithTemplateWork G height sample
    let out := prepareEarlyDistanceTableWithRoundingWork G height sample
    out.2 = plain.2 ∧ ∀ P,
      (out.1 P).1 = (plain.1 P).1 ∧
        (out.1 P).2 ≤ (plain.1 P).2+(P.length+1)*roundingComparisonPolynomial (Fintype.card V) height := by
  let query := readDistanceRow (distanceTableWithSearchWork G).1
  let dist := fun d => (query d).1
  have known (d : V × V) : dist d = hops G d.1 d.2 :=
    (distanceTableReadWithSearchWork_spec G d).1
  let template := heightForestWithDistanceWork (historyDistanceRead query)
    (historyDistanceRead (fun d => query d.swap)) height
  let links := template.1
  have correct : links = heightForestFromDistances dist height :=
    (heightForestWithDistanceTableWork_spec G height).1.trans (heightForestFromDistances_eq G dist known height).symm
  let weight := forestWeightFromDistances (height := height) dist
  let priced := pricedForestFromWeights links weight
  let free := freeForestFromWeights links weight
  let networkWeight := networkWeightFromForestWeights weight
  let sizes := preparedScaleAndFuel priced networkWeight
  let scale := sizes.1
  let fuel := sizes.2
  have scaleEq : scale = forestScale G height := forestScaleFromWeights_eq G dist known height links correct
  let seed : ForestTrialArray V height scale (earlyTrialCount V height) :=
    cast (congrArg (fun k => ForestTrialArray V height k (earlyTrialCount V height)) scaleEq.symm) sample
  let oldMetric := earlyMetricWithPreparedInputs links weight priced free networkWeight scale fuel seed
  let newMetric := earlyMetricWithPreparedRoundingWork links query priced free networkWeight scale fuel seed
  let B := roundingComparisonPolynomial (Fintype.card V) height
  have metric (P : List (V × V)) : (newMetric P).1 = (oldMetric P).1 ∧
      (newMetric P).2 ≤ (oldMetric P).2+B := by
    let frac := forestFractionalWithPreparedInputs priced free networkWeight scale fuel P
    obtain ⟨same, work⟩ := roundedForestTrialsWithWork_spec links (forestWeightWithDistanceWork query)
      frac.1.1 scale (earlyTrialCount V height) (Fintype.card V^2)
      (fun _ => (distanceTableReadWithSearchWork_spec G _).2) seed
    exact ⟨same, Nat.add_le_add_left (work.trans (roundingComparisonBound_le G height links scale scaleEq)) frac.2⟩
  refine ⟨rfl,?_⟩
  intro P
  exact earlyRoundedGraphWithSearchWorkFromMetric_compare G height oldMetric newMetric B metric P

/-- One weighted request's capacity table visits and weight reads have this
polynomial bound for fixed height. -/
def capacityComparisonPolynomial (n height : ℕ) : ℕ :=
  let F := (n*2)*((height+1)*n^height)
  let S := 1+n*F^2
  ((S+1)*S+1)*capacityTableWorkBound (3*F) (F^2) (n^2)

private theorem capacityComparisonBound_le (G : Arcs V) (height : ℕ)
    (links : Arcs (HeightForestVertex V height))
    (weight : HeightForestVertex V height × HeightForestVertex V height → ℕ)
    (scaleEq : (preparedScaleAndFuel (pricedForestFromWeights links weight)
      (networkWeightFromForestWeights weight)).1 = forestScale G height) :
    let priced := pricedForestFromWeights links weight
    let sizes := preparedScaleAndFuel priced (networkWeightFromForestWeights weight)
    sizes.2*capacityTableWorkBound (Fintype.card (ForestNetworkVertex V height)) priced.card (Fintype.card V^2) ≤
      capacityComparisonPolynomial (Fintype.card V) height := by
  let n := Fintype.card V
  let F := (n*2)*((height+1)*n^height)
  let S := 1+n*F^2
  have forest : Fintype.card (HeightForestVertex V height) ≤ F := by
    cases isEmpty_or_nonempty V with
    | inl empty => simp [HeightForestVertex]
    | inr ne => exact heightForestVertex_card_le V height
  have network : Fintype.card (ForestNetworkVertex V height) ≤ 3*F := by
    simpa [ForestNetworkVertex] using Nat.mul_le_mul_left 3 forest
  have linkBound : links.card ≤ F^2 := by
    have atMost := card_le_univ links
    rw [Fintype.card_prod, ← pow_two] at atMost
    exact atMost.trans (Nat.pow_le_pow_left forest _)
  let priced := pricedForestFromWeights links weight
  have pricedBound : priced.card ≤ F^2 := by
    unfold priced pricedForestFromWeights
    rw [card_map]
    exact (card_filter_le _ _).trans linkBound
  let total := ∑ a ∈ priced, networkWeightFromForestWeights weight a
  have scale : max 1 total ≤ S := by
    change (preparedScaleAndFuel priced (networkWeightFromForestWeights weight)).1 ≤ S
    rw [scaleEq]
    apply (forestNetworkScale_le G height).trans
    refine max_le (Nat.le_add_right _ _) (le_trans ?_ (Nat.le_add_left _ _))
    gcongr
  have totalBound : total ≤ S := (le_max_right 1 total).trans scale
  have logBound := (Nat.log2_le_self (max 1 total)).trans scale
  change (((max 1 total).log2+1)*total+1)*capacityTableWorkBound
    (Fintype.card (ForestNetworkVertex V height)) priced.card (n^2) ≤
    ((S+1)*S+1)*capacityTableWorkBound (3*F) (F^2) (n^2)
  unfold capacityTableWorkBound
  gcongr

/-- Capacity table construction preserves the rounded early graph and charges
one pass over the ordered pairs and the original weight reads it makes. -/
theorem prepareEarlyDistanceTableWithCapacityWork_spec (G : Arcs V) (height : ℕ)
    (sample : EarlyRoundSample G height) :
    let rounded := prepareEarlyDistanceTableWithRoundingWork G height sample
    let out := prepareEarlyDistanceTableWithCapacityWork G height sample
    out.2 = rounded.2 ∧ ∀ P,
      (out.1 P).1 = (rounded.1 P).1 ∧
        (out.1 P).2 ≤ (rounded.1 P).2+(P.length+1)*(P.length*capacityComparisonPolynomial (Fintype.card V) height) := by
  let query := readDistanceRow (distanceTableWithSearchWork G).1
  let dist := fun d => (query d).1
  have known (d : V × V) : dist d = hops G d.1 d.2 :=
    (distanceTableReadWithSearchWork_spec G d).1
  let template := heightForestWithDistanceWork (historyDistanceRead query)
    (historyDistanceRead (fun d => query d.swap)) height
  let links := template.1
  have correct : links = heightForestFromDistances dist height :=
    (heightForestWithDistanceTableWork_spec G height).1.trans (heightForestFromDistances_eq G dist known height).symm
  let weight := forestWeightFromDistances (height := height) dist
  let priced := pricedForestFromWeights links weight
  let free := freeForestFromWeights links weight
  let networkWeight := networkWeightFromForestWeights weight
  let sizes := preparedScaleAndFuel priced networkWeight
  let scale := sizes.1
  let fuel := sizes.2
  have scaleEq : scale = forestScale G height := forestScaleFromWeights_eq G dist known height links correct
  let seed : ForestTrialArray V height scale (earlyTrialCount V height) :=
    cast (congrArg (fun k => ForestTrialArray V height k (earlyTrialCount V height)) scaleEq.symm) sample
  let oldMetric := earlyMetricWithPreparedRoundingWork links query priced free networkWeight scale fuel seed
  let newMetric := earlyMetricWithPreparedCapacityWork links query priced free scale fuel seed
  let B := capacityComparisonPolynomial (Fintype.card V) height
  let C := capacityTableWorkBound (Fintype.card (ForestNetworkVertex V height)) priced.card (Fintype.card V^2)
  have weightBound : fuel*C ≤ B :=
    capacityComparisonBound_le G height links weight scaleEq
  refine ⟨rfl,?_⟩
  intro P
  refine earlyRoundedGraphWithSearchWorkFromMetric_compareOnPrefixes G height oldMetric newMetric (P.length*B) P ?_
  intro Q present
  let evaluate := fun charges => roundedForestTrialsWithWork links (forestWeightWithDistanceWork query)
    charges scale (earlyTrialCount V height) seed
  let old := forestFractionalWithPreparedInputs priced free networkWeight scale fuel Q
  let out := weightedNetworkRunAtScaleWithCapacityWork priced (networkWeightWithDistanceWork query)
    scale fuel (Q.map (requestOnFreeForest free)) (fun _ => 0)
  obtain ⟨same,charge⟩ := weightedNetworkRunAtScaleWithCapacityWork_spec priced (networkWeightWithDistanceWork query)
    scale fuel (Fintype.card V^2) (fun _ => (distanceTableReadWithSearchWork_spec G _).2)
    (Q.map (requestOnFreeForest free)) (fun _ => 0)
  have identical : out.1 = old.1 := same
  have search : out.2 ≤ old.2+Q.length*(fuel*C) := by
    have length : (Q.map (requestOnFreeForest free)).length = Q.length := List.length_map _
    rw [← length]
    exact charge
  have shorter := ((List.mem_inits _ _).mp present).length_le
  have counted := search.trans (Nat.add_le_add_left (Nat.mul_le_mul shorter weightBound) old.2)
  change (evaluate out.1.1).1 = (evaluate old.1.1).1 ∧
    out.2+(evaluate out.1.1).2 ≤ old.2+(evaluate old.1.1).2+P.length*B
  rw [identical]
  refine ⟨rfl,?_⟩
  omega

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
