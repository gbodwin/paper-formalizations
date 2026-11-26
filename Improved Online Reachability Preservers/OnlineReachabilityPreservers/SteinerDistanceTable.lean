import OnlineReachabilityPreservers.SteinerWeightedChargeWork
import OnlineReachabilityPreservers.SteinerCapacityWork
import OnlineReachabilityPreservers.SteinerEarlyReplay
import OnlineReachabilityPreservers.SteinerRoundingWork
import OnlineReachabilityPreservers.SteinerTemplateWork
import OnlineReachabilityPreservers.SteinerForestAttachmentsWork
import OnlineReachabilityPreservers.SteinerForestLabelWork
import OnlineReachabilityPreservers.SteinerForestExpansionWork

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

/-- The stored rows follow the canonical vertex order and contain the exact hop values. -/
theorem distanceTableWithSearchWork_rows (G : Arcs V) :
    let vertices := (univ : Finset V).sort
    (distanceTableWithSearchWork G).1 =
      vertices.flatMap (fun s => vertices.map fun t => ((s,t),hops G s t)) := by
  unfold distanceTableWithSearchWork vertexPairList
  simp only [List.map_map, List.map_flatMap]
  apply List.flatMap_congr
  intro s _
  apply List.map_congr_left
  intro t _
  exact congrArg (fun d => ((s,t),d)) (hopsWithSearchWork_spec G s t).1

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

/-- The priced arcs, free arcs, scale, separator fuel, and original table-read tally. -/
abbrev ForestWeightPlan (V : Type*) (height : ℕ) :=
  (Arcs (ForestNetworkVertex V height) × Arcs (ForestNetworkVertex V height)) ×
    (ℕ × ℕ) × ℕ

/-- Evaluate each link once to build both weighted classes and their fixed
scale and fuel. The extra charge counts the original weight reads. -/
def prepareForestWeights (links : Arcs (HeightForestVertex V height))
    (read : HeightForestVertex V height × HeightForestVertex V height → ℕ × ℕ) :
    ForestWeightPlan V height :=
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

omit [Fintype V] in
/-- The ordinary plan partitions the forest arcs and retains both totals. -/
theorem prepareForestWeights_exact (links : Arcs (HeightForestVertex V height))
    (read : HeightForestVertex V height × HeightForestVertex V height → ℕ × ℕ) :
    let out := prepareForestWeights links read
    let copy := (forestNetworkCopy (V := V) (height := height)).prodMap (forestNetworkCopy (V := V) (height := height))
    let total := ∑ e ∈ links, (read e).1
    let scale := max 1 total
    out = (((links.filter fun e => 0 < (read e).1).map copy,
      (links.filter fun e => (read e).1 = 0).map copy),
      (scale,(scale.log2+1)*total+1),∑ e ∈ links, (read e).2) := by
  dsimp only [prepareForestWeights]
  rw [selectedPreparedForestArcs_eq links read, selectedPreparedForestArcs_eq links read, sum_map]
  rw [sum_map]
  rfl

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

private abbrev SteinerSeedPreparationResult (G : Arcs V) (height : ℕ) (Seed Result : Type*) :=
  {scale : ℕ // scale = forestScale G height} ×
    (Seed → List (V × V) → Result) × ℕ × ℕ × ℕ

/-- Shared forest scale, early prefix evaluator, and the three preparation tallies. -/
abbrev SteinerSeedPreparation (G : Arcs V) (height : ℕ) :=
  SteinerSeedPreparationResult G height (EarlyRoundSample G height) (Arcs V × ℕ)

private def prepareEarlyWithPlan {SeedAt : ℕ → Type*} {Result : Type*} (G : Arcs V) (height : ℕ)
    (table : List ((V × V) × ℕ) × ℕ) (rows : table.1 = (distanceTableWithSearchWork G).1)
    (template : Arcs (HeightForestVertex V height) × ℕ) (exactForest : template.1 = heightForest G height)
    (plan : ForestWeightPlan V height)
    (matchesPlan : plan = prepareForestWeights template.1 (forestWeightWithDistanceWork (readDistanceRow table.1)))
    (evaluate : Arcs (HeightForestVertex V height) → (V × V → ℕ × ℕ) →
      Arcs (ForestNetworkVertex V height) → Arcs (ForestNetworkVertex V height) → (scale fuel : ℕ) →
      SeedAt scale → List (V × V) → Result) :
    SteinerSeedPreparationResult G height (SeedAt (forestScale G height)) Result :=
  let query := readDistanceRow table.1
  let dist := fun d => (query d).1
  let known : ∀ d : V × V, dist d = hops G d.1 d.2 :=
    fun d => by
      change (readDistanceRow table.1 d).1 = _
      rw [rows]
      exact (distanceTableReadWithSearchWork_spec G d).1
  let links := template.1
  let correct : links = heightForestFromDistances dist height :=
    exactForest.trans (heightForestFromDistances_eq G dist known height).symm
  let spec := prepareForestWeights_spec links (forestWeightWithDistanceWork query) (Fintype.card V^2)
    (fun e => by
      let d := (heightForestLabel e.1,heightForestLabel e.2)
      change (readDistanceRow table.1 d).2 ≤ _
      rw [rows]
      exact (distanceTableReadWithSearchWork_spec G d).2)
  let scale : plan.2.1.1 = forestScale G height :=
    (congrArg (fun x => x.2.1.1) matchesPlan).trans
      ((congrArg Prod.fst spec.2.2.1).trans (forestScaleFromWeights_eq G dist known height links correct))
  let build := fun sample : SeedAt (forestScale G height) =>
    let seed := cast (congrArg SeedAt scale.symm) sample
    evaluate links query plan.1.1 plan.1.2 plan.2.1.1 plan.2.1.2 seed
  (⟨plan.2.1.1,scale⟩,build,table.2,template.2,plan.2.2)

/-- Assemble the early evaluator with an already constructed weighted plan. -/
def prepareEarlyDistanceTableForSeedFromWeights (G : Arcs V) (height : ℕ)
    (table : List ((V × V) × ℕ) × ℕ) (rows : table.1 = (distanceTableWithSearchWork G).1)
    (template : Arcs (HeightForestVertex V height) × ℕ) (exactForest : template.1 = heightForest G height)
    (plan : ForestWeightPlan V height)
    (matchesPlan : plan = prepareForestWeights template.1 (forestWeightWithDistanceWork (readDistanceRow table.1))) :
    SteinerSeedPreparation G height :=
  prepareEarlyWithPlan (SeedAt := fun s => ForestTrialArray V height s (earlyTrialCount V height))
    G height table rows template exactForest plan matchesPlan
    (fun links query priced free scale fuel seed => earlyRoundedGraphWithSearchWorkFromMetric G height
      (earlyMetricWithPreparedCapacityWork links query priced free scale fuel seed))

@[inline] private def earlyMetricWithPreparedCapacityTally {height : ℕ}
    (read : V × V → ℕ × ℕ) (priced free : Arcs (ForestNetworkVertex V height))
    (scale fuel : ℕ)
    (round : (ForestNetworkVertex V height × ForestNetworkVertex V height → ℕ) →
      Arcs (HeightForestVertex V height) × ℕ × ℕ)
    (P : List (V × V)) : Arcs (HeightForestVertex V height) × ℕ × ℕ :=
  let out := weightedNetworkRunAtScaleWithCapacityWork priced (networkWeightWithDistanceWork read)
    scale fuel (P.map (requestOnFreeForest free)) (fun _ => 0)
  let rounded := round out.1.1
  (rounded.1,out.2+rounded.2.1,rounded.2.2)

private def earlyMetricWithPreparedCapacitySeedReads {height : ℕ} (links : Arcs (HeightForestVertex V height))
    (read : V × V → ℕ × ℕ) (priced free : Arcs (ForestNetworkVertex V height))
    (scale fuel : ℕ) (seed : ForestTrialArray V height scale (earlyTrialCount V height))
    (P : List (V × V)) : Arcs (HeightForestVertex V height) × ℕ × ℕ :=
  earlyMetricWithPreparedCapacityTally read priced free scale fuel
    (fun charges => roundedForestTrialsWithSeedReads links (forestWeightWithDistanceWork read) charges scale
      (earlyTrialCount V height) seed) P

private theorem earlyMetricWithPreparedCapacitySeedReads_spec {height : ℕ} (links : Arcs (HeightForestVertex V height))
    (read : V × V → ℕ × ℕ) (priced free : Arcs (ForestNetworkVertex V height))
    (scale fuel : ℕ) (seed : ForestTrialArray V height scale (earlyTrialCount V height))
    (P : List (V × V)) :
    let out := earlyMetricWithPreparedCapacitySeedReads links read priced free scale fuel seed P
    (out.1,out.2.1) = earlyMetricWithPreparedCapacityWork links read priced free scale fuel seed P ∧
      out.2.2 ≤ earlyTrialCount V height*(links.card*((scale.log2+1)*(height+2))) := by
  let out := weightedNetworkRunAtScaleWithCapacityWork priced (networkWeightWithDistanceWork read)
    scale fuel (P.map (requestOnFreeForest free)) (fun _ => 0)
  obtain ⟨same,work⟩ := roundedForestTrialsWithSeedReads_spec links (forestWeightWithDistanceWork read)
    out.1.1 scale (earlyTrialCount V height) seed
  exact ⟨congrArg (fun x => (x.1,out.2+x.2)) same,work⟩

private def earlyMetricWithPreparedCapacitySeedWork {height : ℕ} (links : Arcs (HeightForestVertex V height))
    (read : V × V → ℕ × ℕ) (priced free : Arcs (ForestNetworkVertex V height))
    (scale fuel : ℕ) (seed : ForestTrialArrayWithSeedWork V height scale (earlyTrialCount V height))
    (P : List (V × V)) : Arcs (HeightForestVertex V height) × ℕ × ℕ :=
  earlyMetricWithPreparedCapacityTally read priced free scale fuel
    (fun charges => roundedForestTrialsWithSeedWork links (forestWeightWithDistanceWork read) charges scale
      (earlyTrialCount V height) seed) P

private theorem earlyMetricWithPreparedCapacitySeedWork_spec {height : ℕ} (links : Arcs (HeightForestVertex V height))
    (read : V × V → ℕ × ℕ) (priced free : Arcs (ForestNetworkVertex V height))
    (scale fuel : ℕ) (seed : ForestTrialArrayWithSeedWork V height scale (earlyTrialCount V height))
    (B : ℕ) (cap : ∀ i, forestSampleWorkBound (seed i) B) (P : List (V × V)) :
    let out := earlyMetricWithPreparedCapacitySeedWork links read priced free scale fuel seed P
    let plain := fun i => forestRoundingSampleValues scale (seed i)
    (out.1,out.2.1) = earlyMetricWithPreparedCapacityWork links read priced free scale fuel plain P ∧
      out.2.2 ≤ earlyTrialCount V height*(links.card*((scale.log2+1)*((height+2)*B))) := by
  let out := weightedNetworkRunAtScaleWithCapacityWork priced (networkWeightWithDistanceWork read)
    scale fuel (P.map (requestOnFreeForest free)) (fun _ => 0)
  obtain ⟨same,work⟩ := roundedForestTrialsWithSeedWork_spec links (forestWeightWithDistanceWork read)
    out.1.1 scale (earlyTrialCount V height) seed B cap
  exact ⟨congrArg (fun x => (x.1,out.2+x.2)) same,work⟩

/-- The seed-position reads of one metric purchase computation. -/
def earlyRoundingSeedReadBound (G : Arcs V) (height : ℕ) : ℕ :=
  earlyTrialCount V height*((heightForest G height).card*(((forestScale G height).log2+1)*(height+2)))

/-- The seed-read allowance for metric rounding is polynomial in the
vertex count at each fixed height. -/
def earlyRoundingSeedReadPolynomial (n height : ℕ) : ℕ :=
  let forest := (n*2)*((height+1)*n^height)
  16*(height+1)^2*(n+1) * (forest^2*((2+n*forest^2)*(height+2)))

theorem earlyRoundingSeedReadBound_le (G : Arcs V) (height : ℕ) :
    earlyRoundingSeedReadBound G height ≤ earlyRoundingSeedReadPolynomial (Fintype.card V) height := by
  let n := Fintype.card V
  let forest := (n*2)*((height+1)*n^height)
  have size : Fintype.card (HeightForestVertex V height) ≤ forest := by
    cases isEmpty_or_nonempty V with
    | inl empty => simp [HeightForestVertex]
    | inr nonempty => exact heightForestVertex_card_le V height
  have edges : (heightForest G height).card ≤ forest^2 := by
    have bound : (heightForest G height).card ≤ Fintype.card (HeightForestVertex V height)^2 := by
      simpa only [Fintype.card_prod,pow_two] using card_le_univ (heightForest G height)
    exact bound.trans (Nat.pow_le_pow_left size 2)
  have scale : forestScale G height ≤ 1+n*forest^2 := by
    apply (forestNetworkScale_le G height).trans
    exact max_le (by omega) ((Nat.mul_le_mul_left n (Nat.pow_le_pow_left size 2)).trans (by omega))
  have width : (forestScale G height).log2+1 ≤ 2+n*forest^2 := by
    have log := Nat.log2_le_self (forestScale G height)
    omega
  unfold earlyRoundingSeedReadBound earlyRoundingSeedReadPolynomial earlyTrialCount
  dsimp only
  gcongr
  exact Nat.log2_le_self n

/-- The usual weighted preparation with a separate seed read tally in
its early prefix evaluator. -/
abbrev SteinerSeedPreparationWithSeedReads (G : Arcs V) (height : ℕ) :=
  SteinerSeedPreparationResult G height (EarlyRoundSample G height) (Arcs V × ℕ × ℕ)

/-- Build the early evaluator with the supplied weighted plan. -/
def prepareEarlyDistanceTableForSeedFromWeightsWithSeedReads (G : Arcs V) (height : ℕ)
    (table : List ((V × V) × ℕ) × ℕ) (rows : table.1 = (distanceTableWithSearchWork G).1)
    (template : Arcs (HeightForestVertex V height) × ℕ) (exactForest : template.1 = heightForest G height)
    (plan : ForestWeightPlan V height)
    (matchesPlan : plan = prepareForestWeights template.1 (forestWeightWithDistanceWork (readDistanceRow table.1))) :
    SteinerSeedPreparationWithSeedReads G height :=
  prepareEarlyWithPlan (SeedAt := fun s => ForestTrialArray V height s (earlyTrialCount V height))
    G height table rows template exactForest plan matchesPlan
    (fun links query priced free scale fuel seed => earlyRoundedGraphWithSeedReadsFromMetric G height
      (earlyMetricWithPreparedCapacitySeedReads links query priced free scale fuel seed))

theorem prepareEarlyDistanceTableForSeedFromWeightsWithSeedReads_spec (G : Arcs V) (height : ℕ)
    (table : List ((V × V) × ℕ) × ℕ) (rows : table.1 = (distanceTableWithSearchWork G).1)
    (template : Arcs (HeightForestVertex V height) × ℕ) (exactForest : template.1 = heightForest G height)
    (plan : ForestWeightPlan V height)
    (matchesPlan : plan = prepareForestWeights template.1 (forestWeightWithDistanceWork (readDistanceRow table.1))) :
    let prepared := prepareEarlyDistanceTableForSeedFromWeightsWithSeedReads G height table rows template exactForest plan matchesPlan
    let old := prepareEarlyDistanceTableForSeedFromWeights G height table rows template exactForest plan matchesPlan
    prepared.1 = old.1 ∧ prepared.2.2 = old.2.2 ∧ ∀ (sample : EarlyRoundSample G height) (D : List (V × V)),
      let out := prepared.2.1 sample D
      (out.1,out.2.1) = old.2.1 sample D ∧ out.2.2 ≤ (D.length+1)*earlyRoundingSeedReadBound G height := by
  intro prepared old
  refine ⟨rfl,rfl,?_⟩
  intro sample D
  let seed : ForestTrialArray V height plan.2.1.1 (earlyTrialCount V height) :=
    cast (congrArg (fun k => ForestTrialArray V height k (earlyTrialCount V height)) old.1.property.symm) sample
  let metric := earlyMetricWithPreparedCapacitySeedReads template.1 (readDistanceRow table.1)
    plan.1.1 plan.1.2 plan.2.1.1 plan.2.1.2 seed
  have each (P : List (V × V)) := earlyMetricWithPreparedCapacitySeedReads_spec template.1 (readDistanceRow table.1)
    plan.1.1 plan.1.2 plan.2.1.1 plan.2.1.2 seed P
  obtain ⟨same,work⟩ := earlyRoundedGraphWithSeedReadsFromMetric_spec G height metric D
    (earlyTrialCount V height*(template.1.card*((plan.2.1.1.log2+1)*(height+2)))) (fun P _ => (each P).2)
  refine ⟨same.trans (congrArg (fun f => earlyRoundedGraphWithSearchWorkFromMetric G height f D)
    (funext fun P => (each P).1)),?_⟩
  change (earlyRoundedGraphWithSeedReadsFromMetric G height metric D).2.2 ≤
    (D.length+1)*earlyRoundingSeedReadBound G height
  have scale_eq : plan.2.1.1 = forestScale G height := old.1.property
  simpa only [earlyRoundingSeedReadBound,exactForest,scale_eq] using work

/-- The same preparation with early seed access costs passed to the prefix evaluator. -/
abbrev SteinerSeedPreparationWithSeedWork (G : Arcs V) (height : ℕ) :=
  SteinerSeedPreparationResult G height
    (ForestTrialArrayWithSeedWork V height (forestScale G height) (earlyTrialCount V height)) (Arcs V × ℕ × ℕ)

def prepareEarlyDistanceTableForSeedFromWeightsWithSeedWork (G : Arcs V) (height : ℕ)
    (table : List ((V × V) × ℕ) × ℕ) (rows : table.1 = (distanceTableWithSearchWork G).1)
    (template : Arcs (HeightForestVertex V height) × ℕ) (exactForest : template.1 = heightForest G height)
    (plan : ForestWeightPlan V height)
    (matchesPlan : plan = prepareForestWeights template.1 (forestWeightWithDistanceWork (readDistanceRow table.1))) :
    SteinerSeedPreparationWithSeedWork G height :=
  prepareEarlyWithPlan (SeedAt := fun s => ForestTrialArrayWithSeedWork V height s (earlyTrialCount V height))
    G height table rows template exactForest plan matchesPlan
    (fun links query priced free scale fuel seed => earlyRoundedGraphWithSeedReadsFromMetric G height
      (earlyMetricWithPreparedCapacitySeedWork links query priced free scale fuel seed))

omit [LinearOrder V] [Fintype V] in
private theorem castForestTrialWork_spec {height trials s t : ℕ} (same : s = t)
    (samples : ForestTrialArrayWithSeedWork V height s trials) (B : ℕ)
    (cap : ∀ i, forestSampleWorkBound (samples i) B) :
    let typed := cast (congrArg (fun k => ForestTrialArrayWithSeedWork V height k trials) same) samples
    (∀ i, forestSampleWorkBound (typed i) B) ∧
      (fun i => forestRoundingSampleValues t (typed i)) =
        cast (congrArg (fun k => ForestTrialArray V height k trials) same)
          (fun i => forestRoundingSampleValues s (samples i)) := by
  subst t
  exact ⟨cap,rfl⟩

theorem prepareEarlyDistanceTableForSeedFromWeightsWithSeedWork_spec (G : Arcs V) (height : ℕ)
    (table : List ((V × V) × ℕ) × ℕ) (rows : table.1 = (distanceTableWithSearchWork G).1)
    (template : Arcs (HeightForestVertex V height) × ℕ) (exactForest : template.1 = heightForest G height)
    (plan : ForestWeightPlan V height)
    (matchesPlan : plan = prepareForestWeights template.1 (forestWeightWithDistanceWork (readDistanceRow table.1))) :
    let prepared := prepareEarlyDistanceTableForSeedFromWeightsWithSeedWork G height table rows template exactForest plan matchesPlan
    let old := prepareEarlyDistanceTableForSeedFromWeights G height table rows template exactForest plan matchesPlan
    prepared.1 = old.1 ∧ prepared.2.2 = old.2.2 ∧
    ∀ samples B, (∀ i, forestSampleWorkBound (samples i) B) → ∀ D,
      let out := prepared.2.1 samples D
      let plain := fun i => forestRoundingSampleValues (forestScale G height) (samples i)
      (out.1,out.2.1) = old.2.1 plain D ∧ out.2.2 ≤ (D.length+1)*(earlyRoundingSeedReadBound G height*B) := by
  intro prepared old
  refine ⟨rfl,rfl,?_⟩
  intro samples B cap D
  have scale_eq : plan.2.1.1 = forestScale G height := old.1.property
  let seed : ForestTrialArrayWithSeedWork V height plan.2.1.1 (earlyTrialCount V height) :=
    cast (congrArg (fun k => ForestTrialArrayWithSeedWork V height k (earlyTrialCount V height)) scale_eq.symm) samples
  let metric := earlyMetricWithPreparedCapacitySeedWork template.1 (readDistanceRow table.1)
    plan.1.1 plan.1.2 plan.2.1.1 plan.2.1.2 seed
  obtain ⟨queryCap,castValues⟩ := castForestTrialWork_spec scale_eq.symm samples B cap
  have each (P : List (V × V)) := earlyMetricWithPreparedCapacitySeedWork_spec template.1 (readDistanceRow table.1)
    plan.1.1 plan.1.2 plan.2.1.1 plan.2.1.2 seed B queryCap P
  obtain ⟨same,work⟩ := earlyRoundedGraphWithSeedReadsFromMetric_spec G height metric D
    (earlyTrialCount V height*(template.1.card*((plan.2.1.1.log2+1)*((height+2)*B)))) (fun P _ => (each P).2)
  have plain (P : List (V × V)) := (each P).1
  change (fun i => forestRoundingSampleValues plan.2.1.1 (seed i)) = _ at castValues
  simp only [castValues] at plain
  refine ⟨same.trans (congrArg (fun f => earlyRoundedGraphWithSearchWorkFromMetric G height f D)
    (funext plain)),?_⟩
  change (earlyRoundedGraphWithSeedReadsFromMetric G height metric D).2.2 ≤
    (D.length+1)*(earlyRoundingSeedReadBound G height*B)
  refine work.trans_eq ?_
  rw [earlyRoundingSeedReadBound,exactForest,scale_eq]
  ring

/-- Finish the weighted plan from the exact stored rows and paired forest.
The two input charges are carried through as supplied by their builders. -/
def prepareEarlyDistanceTableForSeedFrom (G : Arcs V) (height : ℕ)
    (table : List ((V × V) × ℕ) × ℕ) (rows : table.1 = (distanceTableWithSearchWork G).1)
    (template : Arcs (HeightForestVertex V height) × ℕ) (exactForest : template.1 = heightForest G height) :
    SteinerSeedPreparation G height :=
  let plan := prepareForestWeights template.1 (forestWeightWithDistanceWork (readDistanceRow table.1))
  prepareEarlyDistanceTableForSeedFromWeights G height table rows template exactForest plan rfl

theorem prepareEarlyDistanceTableForSeedFromWeights_eq (G : Arcs V) (height : ℕ)
    (table : List ((V × V) × ℕ) × ℕ) (rows : table.1 = (distanceTableWithSearchWork G).1)
    (template : Arcs (HeightForestVertex V height) × ℕ) (exactForest : template.1 = heightForest G height)
    (plan : ForestWeightPlan V height)
    (matchesPlan : plan = prepareForestWeights template.1 (forestWeightWithDistanceWork (readDistanceRow table.1))) :
    prepareEarlyDistanceTableForSeedFromWeights G height table rows template exactForest plan matchesPlan =
      prepareEarlyDistanceTableForSeedFrom G height table rows template exactForest := by
  subst plan
  rfl

/-- Also meter preparation of the weighted link classes, scale, and fuel.
The table, forest, and weighted plan are constructed once. -/
def prepareEarlyDistanceTableForSeed (G : Arcs V) (height : ℕ) :
    SteinerSeedPreparation G height :=
  let table := distanceTableWithSearchWork G
  let query := readDistanceRow table.1
  let template := heightForestWithDistanceWork (historyDistanceRead query)
    (historyDistanceRead (fun d => query d.swap)) height
  prepareEarlyDistanceTableForSeedFrom G height table rfl template
    (heightForestWithDistanceTableWork_spec G height).1

/-- Replacing how the rows and arcs are built preserves the scale, prefix
evaluator, and original weight-read charges. -/
theorem prepareEarlyDistanceTableForSeedFrom_eq (G : Arcs V) (height : ℕ)
    (table : List ((V × V) × ℕ) × ℕ) (rows : table.1 = (distanceTableWithSearchWork G).1)
    (template : Arcs (HeightForestVertex V height) × ℕ) (exactForest : template.1 = heightForest G height) :
    let out := prepareEarlyDistanceTableForSeedFrom G height table rows template exactForest
    let old := prepareEarlyDistanceTableForSeed G height
    out = (old.1,old.2.1,table.2,template.2,old.2.2.2.2) := by
  rcases table with ⟨rowsValue, rowWork⟩
  rcases template with ⟨links, templateWork⟩
  dsimp only at rows exactForest
  subst rowsValue
  have sameLinks := exactForest.trans (heightForestWithDistanceTableWork_spec G height).1.symm
  subst sameLinks
  rfl

/-- Preparation charges are bounded before any seed has been decoded. -/
theorem prepareEarlyDistanceTableForSeed_work_le (G : Arcs V) (height : ℕ) :
    let n := Fintype.card V
    let work := (prepareEarlyDistanceTableForSeed G height).2.2
    work.1 ≤ n^2*((n+1)*n*G.card) ∧
      work.2.1 ≤ n*(2*Fintype.card (HeightNode V height)*height*n^2) ∧
      work.2.2 ≤ Fintype.card (HeightForestVertex V height)^2*n^2 := by
  let read := readDistanceRow (distanceTableWithSearchWork G).1
  let links := (heightForestWithDistanceWork (historyDistanceRead read)
    (historyDistanceRead (fun d => read d.swap)) height).1
  have rows := prepareForestWeights_spec links (forestWeightWithDistanceWork read)
    (Fintype.card V^2) (fun _ => (distanceTableReadWithSearchWork_spec G _).2)
  have arcs : links.card ≤ Fintype.card (HeightForestVertex V height)^2 := by
    simpa only [Fintype.card_prod, pow_two] using card_le_univ links
  exact ⟨distanceTableWithSearchWork_bound G, (heightForestWithDistanceTableWork_spec G height).2,
    rows.2.2.2.trans (Nat.mul_le_mul_right _ arcs)⟩

def prepareEarlyDistanceTableWithWeightWork (G : Arcs V) (height : ℕ) (sample : EarlyRoundSample G height) :
    (List (V × V) → Arcs V × ℕ) × ℕ × ℕ × ℕ :=
  let prepared := prepareEarlyDistanceTableForSeed G height
  (prepared.2.1 sample,prepared.2.2)

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

private abbrev ForestPairKeys (V : Type*) (height : ℕ) :=
  {rows : List (ForestNetworkVertex V height × ForestNetworkVertex V height) // rows.Nodup}

private def earlyMetricWithPreparedHistoryWork {height : ℕ} (keys : ForestPairKeys V height)
    (links : Arcs (HeightForestVertex V height))
    (read : V × V → ℕ × ℕ) (priced free : Arcs (ForestNetworkVertex V height))
    (scale fuel : ℕ) (seed : ForestTrialArrayWithSeedWork V height scale (earlyTrialCount V height))
    (P : List (V × V)) : Arcs (HeightForestVertex V height) × ℕ × ℕ :=
  let fractional := weightedNetworkRunWithHistoryWork keys.val keys.property priced (networkWeightWithDistanceWork read)
    (fun _ => (0,1)) scale fuel (P.map (requestOnFreeForest free))
  let rounded := roundedForestTrialsWithSeedWork links (forestWeightWithDistanceWork read)
    (fun e => (fractional.1.1 e).1) scale (earlyTrialCount V height) seed
  (rounded.1, rounded.2.1, fractional.2 + rounded.2.2 + 5)

/-- Work added by one weighted network run on a forest prefix. Returned
charge reads during rounding carry their own costs. -/
def earlyWeightedHistoryWordBudget (network paid scale fuel weight p : ℕ) : ℕ :=
  let H := p * fuel
  let separator := weightedHistorySeparatorWordBudget network paid scale weight 0 1 H
  p * (fuel * (separator + 10) + 13) + 6 * H + 12 + 5

/-- The per-prefix budget grows with the bounds supplied by preparation. -/
theorem earlyWeightedHistoryWordBudget_le
    {network network' paid paid' scale scale' fuel fuel' weight weight' p p' : ℕ}
    (vertices : network ≤ network') (arcs : paid ≤ paid') (scales : scale ≤ scale')
    (fuels : fuel ≤ fuel') (reads : weight ≤ weight') (prefixes : p ≤ p') :
    earlyWeightedHistoryWordBudget network paid scale fuel weight p ≤
      earlyWeightedHistoryWordBudget network' paid' scale' fuel' weight' p' := by
  have charge := weightedHistorySeparatorWordBudget_le vertices arcs scales reads
    (Nat.mul_le_mul prefixes fuels) 0 1
  unfold earlyWeightedHistoryWordBudget
  dsimp only
  gcongr

private theorem earlyMetricWithPreparedHistoryWork_spec {height : ℕ} (keys : ForestPairKeys V height)
    (complete : ∀ e, e ∈ keys.val) (links : Arcs (HeightForestVertex V height))
    (read : V × V → ℕ × ℕ) (priced free : Arcs (ForestNetworkVertex V height))
    (scale fuel W : ℕ) (weightWork : ∀ d, (read d).2 ≤ W)
    (seed : ForestTrialArrayWithSeedWork V height scale (earlyTrialCount V height))
    (B : ℕ) (seedWork : ∀ i, forestSampleWorkBound (seed i) B) (P : List (V × V)) :
    let out := earlyMetricWithPreparedHistoryWork keys links read priced free scale fuel seed P
    let old := earlyMetricWithPreparedCapacitySeedWork links read priced free scale fuel seed P
    out.1 = old.1 ∧ out.2.1 ≤ old.2.1 ∧
      out.2.2 ≤ earlyWeightedHistoryWordBudget (Fintype.card (ForestNetworkVertex V height))
        priced.card scale fuel W P.length +
        earlyTrialCount V height * (links.card * ((scale.log2 + 1) * ((height + 2) * B))) := by
  let cost := networkWeightWithDistanceWork (height := height) read
  let demands := P.map (requestOnFreeForest free)
  let frac := weightedNetworkRunWithHistoryWork keys.val keys.property priced cost (fun _ => (0,1)) scale fuel demands
  let prior := weightedNetworkRunAtScaleWithCapacityWork priced cost scale fuel demands (fun _ => 0)
  let round := roundedForestTrialsWithSeedWork links (forestWeightWithDistanceWork read)
  let priorRound := round prior.1.1 scale (earlyTrialCount V height) seed
  have work (e : ForestNetworkVertex V height × ForestNetworkVertex V height) : (cost e).2 ≤ W := by
    exact weightWork (heightForestLabel (ofLex e.1).2,heightForestLabel (ofLex e.2).2)
  have before := (weightedNetworkRunAtScaleWithCapacityWork_spec priced cost scale fuel W work demands (fun _ => 0)).1
  obtain ⟨charges, _, fractionalWork⟩ :=
    weightedNetworkRunWithHistoryWork_spec keys.val keys.property complete priced cost
      (fun _ => (0,1)) scale fuel W 0 1 demands work (fun _ => le_rfl) (fun _ => le_rfl)
  have exactFrac : ((fun e => (frac.1.1 e).1), frac.1.2) = prior.1 := charges.trans before.symm
  have exactCharges : (fun e => (frac.1.1 e).1) = prior.1.1 := congrArg Prod.fst exactFrac
  obtain ⟨_, roundingBound⟩ := roundedForestTrialsWithSeedWork_spec links (forestWeightWithDistanceWork read)
    prior.1.1 scale (earlyTrialCount V height) seed B seedWork
  have part : frac.2 + 5 ≤ earlyWeightedHistoryWordBudget (Fintype.card (ForestNetworkVertex V height))
      priced.card scale fuel W P.length := by
    change frac.2 ≤ _ at fractionalWork
    simp only [demands, List.length_map] at fractionalWork
    exact Nat.add_le_add_right fractionalWork 5
  change (round (fun e => (frac.1.1 e).1) scale (earlyTrialCount V height) seed).1 = priorRound.1 ∧
    (round (fun e => (frac.1.1 e).1) scale (earlyTrialCount V height) seed).2.1 ≤ prior.2 + priorRound.2.1 ∧
    frac.2 + (round (fun e => (frac.1.1 e).1) scale (earlyTrialCount V height) seed).2.2 + 5 ≤ _
  rw [exactCharges]
  refine ⟨rfl, Nat.le_add_left _ _, ?_⟩
  have rounding : priorRound.2.2 ≤ _ := roundingBound
  change frac.2 + priorRound.2.2 + 5 ≤ _
  omega

/-- Assemble the early prefix evaluator with explicit ordered-pair keys
and the same stored forest and weighted plan. -/
def prepareEarlyDistanceTableForSeedFromWeightsWithHistoryWork (G : Arcs V) (height : ℕ)
    (keys : ForestPairKeys V height)
    (table : List ((V × V) × ℕ) × ℕ) (rows : table.1 = (distanceTableWithSearchWork G).1)
    (template : Arcs (HeightForestVertex V height) × ℕ) (exactForest : template.1 = heightForest G height)
    (plan : ForestWeightPlan V height)
    (matchesPlan : plan = prepareForestWeights template.1 (forestWeightWithDistanceWork (readDistanceRow table.1))) :
    SteinerSeedPreparationWithSeedWork G height :=
  prepareEarlyWithPlan (SeedAt := fun s => ForestTrialArrayWithSeedWork V height s (earlyTrialCount V height))
    G height table rows template exactForest plan matchesPlan
    (fun links query priced free scale fuel seed => earlyRoundedGraphWithSeedReadsFromMetric G height
      (earlyMetricWithPreparedHistoryWork keys links query priced free scale fuel seed))

theorem prepareEarlyDistanceTableForSeedFromWeightsWithHistoryWork_spec (G : Arcs V) (height : ℕ)
    (keys : ForestPairKeys V height) (complete : ∀ e, e ∈ keys.val)
    (table : List ((V × V) × ℕ) × ℕ) (rows : table.1 = (distanceTableWithSearchWork G).1)
    (template : Arcs (HeightForestVertex V height) × ℕ) (exactForest : template.1 = heightForest G height)
    (plan : ForestWeightPlan V height)
    (matchesPlan : plan = prepareForestWeights template.1 (forestWeightWithDistanceWork (readDistanceRow table.1))) :
    let prepared := prepareEarlyDistanceTableForSeedFromWeightsWithHistoryWork G height keys
      table rows template exactForest plan matchesPlan
    let old := prepareEarlyDistanceTableForSeedFromWeightsWithSeedWork G height
      table rows template exactForest plan matchesPlan
    prepared.1 = old.1 ∧ prepared.2.2 = old.2.2 ∧
    ∀ (samples : ForestTrialArrayWithSeedWork V height (forestScale G height) (earlyTrialCount V height))
      (B : ℕ), (∀ i, forestSampleWorkBound (samples i) B) → ∀ (D : List (V × V)),
      let out := prepared.2.1 samples D
      let prior := old.2.1 samples D
      out.1 = prior.1 ∧ out.2.1 ≤ prior.2.1 ∧
      out.2.2 ≤ (D.length+1) * (earlyWeightedHistoryWordBudget (Fintype.card (ForestNetworkVertex V height))
        plan.1.1.card plan.2.1.1 plan.2.1.2 ((Fintype.card V)^2) D.length + earlyRoundingSeedReadBound G height * B) := by
  intro prepared old
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [prepared, old, prepareEarlyDistanceTableForSeedFromWeightsWithHistoryWork,
      prepareEarlyDistanceTableForSeedFromWeightsWithSeedWork, prepareEarlyWithPlan]
  · dsimp only [prepared, old, prepareEarlyDistanceTableForSeedFromWeightsWithHistoryWork,
      prepareEarlyDistanceTableForSeedFromWeightsWithSeedWork, prepareEarlyWithPlan]
  intro samples B cap D
  let net := Fintype.card (ForestNetworkVertex V height)
  let W := (Fintype.card V)^2
  let read := readDistanceRow table.1
  let priced := plan.1.1
  let scale := plan.2.1.1
  let fuel := plan.2.1.2
  have scale_eq : scale = forestScale G height := old.1.property
  let seed : ForestTrialArrayWithSeedWork V height scale (earlyTrialCount V height) :=
    cast (congrArg (fun k => ForestTrialArrayWithSeedWork V height k (earlyTrialCount V height)) scale_eq.symm) samples
  let metricNew := earlyMetricWithPreparedHistoryWork keys template.1 read priced plan.1.2 scale fuel seed
  let metricOld := earlyMetricWithPreparedCapacitySeedWork template.1 read priced plan.1.2 scale fuel seed
  let ready := earlyWeightedHistoryWordBudget net priced.card scale fuel W D.length
  let round := earlyTrialCount V height * (template.1.card * ((scale.log2 + 1) * ((height + 2) * B)))
  have readBound (d : V × V) : (read d).2 ≤ W := by
    change (readDistanceRow table.1 d).2 ≤ W
    rw [rows]
    exact (distanceTableReadWithSearchWork_spec G d).2
  obtain ⟨cap', _⟩ := castForestTrialWork_spec scale_eq.symm samples B cap
  have each (P : List (V × V)) :=
    earlyMetricWithPreparedHistoryWork_spec keys complete template.1 read priced plan.1.2 scale fuel W readBound seed B cap' P
  have newBound (P : List (V × V)) (on : P ∈ D.inits) : (metricNew P).2.2 ≤ ready + round := by
    have shorter : P.length ≤ D.length := ((List.mem_inits _ _).mp on).length_le
    have booked : earlyWeightedHistoryWordBudget net priced.card scale fuel W P.length ≤ ready :=
      earlyWeightedHistoryWordBudget_le le_rfl le_rfl le_rfl le_rfl le_rfl shorter
    exact (each P).2.2.trans (Nat.add_le_add_right booked _)
  have oldBound (P : List (V × V)) : (metricOld P).2.2 ≤ round :=
    (earlyMetricWithPreparedCapacitySeedWork_spec template.1 read priced plan.1.2 scale fuel seed B cap' P).2
  obtain ⟨newMatch, newWork⟩ := earlyRoundedGraphWithSeedReadsFromMetric_spec G height metricNew D _ newBound
  obtain ⟨oldMatch, _⟩ := earlyRoundedGraphWithSeedReadsFromMetric_spec G height metricOld D round
    (fun P _ => oldBound P)
  have same := earlyRoundedGraphWithSearchWorkFromMetric_compare G height
    (fun P => ((metricOld P).1, (metricOld P).2.1)) (fun P => ((metricNew P).1, (metricNew P).2.1))
    0 (fun P => ⟨(each P).1, by simpa only [Nat.add_zero] using (each P).2.1⟩) D
  change (earlyRoundedGraphWithSeedReadsFromMetric G height metricNew D).1 =
      (earlyRoundedGraphWithSeedReadsFromMetric G height metricOld D).1 ∧
    (earlyRoundedGraphWithSeedReadsFromMetric G height metricNew D).2.1 ≤
      (earlyRoundedGraphWithSeedReadsFromMetric G height metricOld D).2.1 ∧
    (earlyRoundedGraphWithSeedReadsFromMetric G height metricNew D).2.2 ≤
      (D.length+1) * (ready + earlyRoundingSeedReadBound G height * B)
  refine ⟨(congrArg Prod.fst newMatch).trans (same.1.trans (congrArg Prod.fst oldMatch).symm), ?_, ?_⟩
  · refine (congrArg Prod.snd newMatch).le.trans ((?_ : _ ≤ _).trans (congrArg Prod.snd oldMatch).symm.le)
    simpa only [Nat.mul_zero, Nat.add_zero] using same.2
  have rounding : round = earlyRoundingSeedReadBound G height * B := by
    unfold round earlyRoundingSeedReadBound
    rw [exactForest, scale_eq]
    ring
  change (earlyRoundedGraphWithSeedReadsFromMetric G height metricNew D).2.2 ≤
    (D.length+1) * (ready + earlyRoundingSeedReadBound G height * B)
  rw [← rounding]
  exact newWork

/-- Meter forest membership, weighted charge reads, and integer
capacity arithmetic across the rounding trials of one metric prefix. -/
def earlyRoundingChargeWordBudget (network links scale fuel weight height trials p : ℕ) : ℕ :=
  let history := p*fuel
  let reads := 4 + history*(12*network^2+14)
  let units := 12*links+weight+6*history+reads+36
  trials*(links*(weight+(scale+1)*(2*(height+1)^2*units)))+2

theorem earlyRoundingChargeWordBudget_le {network network' links links' scale scale' fuel fuel'
    weight weight' height trials trials' p p' : ℕ}
    (vertices : network ≤ network') (edges : links ≤ links') (scales : scale ≤ scale')
    (fuels : fuel ≤ fuel') (weights : weight ≤ weight') (many : trials ≤ trials') (prefixes : p ≤ p') :
    earlyRoundingChargeWordBudget network links scale fuel weight height trials p ≤
      earlyRoundingChargeWordBudget network' links' scale' fuel' weight' height trials' p' := by
  unfold earlyRoundingChargeWordBudget
  dsimp only
  gcongr

private abbrev ForestRequestRows (V : Type*) (height : ℕ) :=
  List (WeightedNetworkDemand (ForestNetworkVertex V height)) × ℕ

private abbrev ForestMetricWeights (V : Type*) (height : ℕ) :=
  (HeightForestVertex V height × HeightForestVertex V height → ℕ × ℕ) ×
    (ForestNetworkVertex V height × ForestNetworkVertex V height → ℕ × ℕ)

@[inline] private def distanceOnlyMetricWeights {height : ℕ} (read : V × V → ℕ × ℕ) :
    ForestMetricWeights V height :=
  (forestWeightWithDistanceWork read,networkWeightWithDistanceWork read)

private def networkDistanceWeightWithWordWork {height : ℕ} (read : V × V → ℕ × ℕ)
    (e : ForestNetworkVertex V height × ForestNetworkVertex V height) : ℕ × ℕ :=
  let out := forestDistanceWeightWithWordWork read ((ofLex e.1).2,(ofLex e.2).2)
  (out.1,out.2+7)

@[inline] private def labelMetricWeights {height : ℕ} (read : V × V → ℕ × ℕ) :
    ForestMetricWeights V height :=
  (forestDistanceWeightWithWordWork read,networkDistanceWeightWithWordWork read)

def forestMetricLabelWordBudget (height readWork : ℕ) : ℕ := 10*height + 8*readWork + 46

omit [LinearOrder V] [Fintype V] in
private theorem labelMetricWeights_spec {height : ℕ} (read : V × V → ℕ × ℕ)
    (B : ℕ) (budget : ∀ d, (read d).2 ≤ B) :
    let measured : ForestMetricWeights V height := labelMetricWeights read
    let old : ForestMetricWeights V height := distanceOnlyMetricWeights read
    (∀ e, (measured.1 e).1 = (old.1 e).1 ∧ (measured.1 e).2 ≤ forestMetricLabelWordBudget height B) ∧
      (∀ e, (measured.2 e).1 = (old.2 e).1 ∧ (measured.2 e).2 ≤ forestMetricLabelWordBudget height B) := by
  constructor
  · intro e
    obtain ⟨value,work⟩ := forestDistanceWeightWithWordWork_spec read B budget e
    exact ⟨value,work.trans (by unfold forestMetricLabelWordBudget; omega)⟩
  · intro e
    obtain ⟨value,work⟩ := forestDistanceWeightWithWordWork_spec read B budget ((ofLex e.1).2,(ofLex e.2).2)
    exact ⟨value,Nat.add_le_add_right work 7⟩

private def MetricWeightReadsMatch {height : ℕ} (read : V × V → ℕ × ℕ)
    (weights : ForestMetricWeights V height) (W : ℕ) : Prop :=
  (∀ e, (weights.1 e).1 = (forestWeightWithDistanceWork read e).1 ∧ (weights.1 e).2 ≤ W) ∧
    (∀ e, (weights.2 e).1 = (networkWeightWithDistanceWork read e).1 ∧ (weights.2 e).2 ≤ W)

omit [LinearOrder V] [Fintype V] in
private theorem distanceOnlyMetricWeights_match {height : ℕ} (read : V × V → ℕ × ℕ) (W : ℕ)
    (budget : ∀ d, (read d).2 ≤ W) : MetricWeightReadsMatch read (distanceOnlyMetricWeights (height := height) read) W :=
  ⟨fun e => ⟨rfl,budget (heightForestLabel e.1,heightForestLabel e.2)⟩,
    fun e => ⟨rfl,budget (heightForestLabel (ofLex e.1).2,heightForestLabel (ofLex e.2).2)⟩⟩

private theorem readDistanceRow_work_bound (G : Arcs V) (table : List ((V × V) × ℕ))
    (rows : table = (distanceTableWithSearchWork G).1) (d : V × V) :
    (readDistanceRow table d).2 ≤ (Fintype.card V)^2 := by
  rw [rows]
  exact (distanceTableReadWithSearchWork_spec G d).2

@[inline] private def earlyMetricWithPreparedRequestsWork {height : ℕ} (keys : ForestPairKeys V height)
    (links : Arcs (HeightForestVertex V height))
    (weights : ForestMetricWeights V height) (priced : Arcs (ForestNetworkVertex V height))
    (scale fuel : ℕ) (seed : ForestTrialArrayWithSeedWork V height scale (earlyTrialCount V height))
    (requests : ForestRequestRows V height) : Arcs (HeightForestVertex V height) × ℕ × ℕ :=
  let fractional := weightedNetworkRunWithHistoryWork keys.val keys.property priced weights.2
    (fun _ => (0,1)) scale fuel requests.1
  let rounded := roundedForestTrialsWithChargeWork links weights.1
    fractional.1.1 scale (earlyTrialCount V height) seed
  (rounded.1, 0, fractional.2 + rounded.2.1 + rounded.2.2 + 7 + requests.2)

private theorem earlyMetricWithPreparedRequestsWork_spec {height : ℕ} (keys : ForestPairKeys V height)
    (complete : ∀ e, e ∈ keys.val) (links : Arcs (HeightForestVertex V height))
    (read : V × V → ℕ × ℕ) (priced free : Arcs (ForestNetworkVertex V height))
    (scale fuel B₀ W : ℕ) (readWork : ∀ d, (read d).2 ≤ B₀)
    (w : ForestMetricWeights V height)
    (forestReads : ∀ e, (w.1 e).1 = (forestWeightWithDistanceWork read e).1 ∧ (w.1 e).2 ≤ W)
    (networkReads : ∀ e, (w.2 e).1 = (networkWeightWithDistanceWork read e).1 ∧ (w.2 e).2 ≤ W)
    (seed : ForestTrialArrayWithSeedWork V height scale (earlyTrialCount V height))
    (B : ℕ) (seedWork : ∀ i, forestSampleWorkBound (seed i) B) (P : List (V × V))
    (requests : ForestRequestRows V height) (requestsEq : requests.1 = P.map (requestOnFreeForest free)) :
    let out := earlyMetricWithPreparedRequestsWork keys links w priced scale fuel seed requests
    let old := earlyMetricWithPreparedHistoryWork keys links read priced free scale fuel seed P
    let N := Fintype.card (ForestNetworkVertex V height)
    let T := earlyTrialCount V height
    out.1 = old.1 ∧ out.2.1 ≤ old.2.1 ∧
      out.2.2 ≤ earlyWeightedHistoryWordBudget N priced.card scale fuel W P.length +
        earlyRoundingChargeWordBudget N links.card scale fuel W height T P.length +
        T*(links.card*((scale.log2+1)*((height+2)*B))) + requests.2 := by
  let n := Fintype.card (ForestNetworkVertex V height)
  let cost := w.2
  let demands := requests.1
  have count : demands.length = P.length := by
    simp only [demands,requestsEq,List.length_map]
  let fractional := weightedNetworkRunWithHistoryWork keys.val keys.property priced cost (fun _ => (0,1)) scale fuel demands
  let weights := w.1
  let rounded := roundedForestTrialsWithChargeWork links weights fractional.1.1 scale (earlyTrialCount V height) seed
  have networkRead (e : ForestNetworkVertex V height × ForestNetworkVertex V height) : (cost e).2 ≤ W := (networkReads e).2
  have forestRead (e : HeightForestVertex V height × HeightForestVertex V height) : (weights e).2 ≤ W := (forestReads e).2
  obtain ⟨cutValues, lookup, chargeWork⟩ := weightedNetworkRunWithHistoryWork_spec keys.val keys.property complete
    priced cost (fun _ => (0,1)) scale fuel W 0 1 demands networkRead (fun _ => le_rfl) (fun _ => le_rfl)
  let H := P.length*fuel
  let C := 4+H*(12*n^2+14)
  have access (e : ForestNetworkVertex V height × ForestNetworkVertex V height) :
      (fractional.1.1 e).1 ≤ H ∧ (fractional.1.1 e).2 ≤ C := by
    have size := weightedNetworkRunWithHistoryWork_charge_le keys.val keys.property complete priced cost
      (fun _ => (0,1)) scale fuel W 0 1 demands networkRead (fun _ => le_rfl) (fun _ => le_rfl) e
    exact ⟨by simpa only [count,Nat.zero_add,H] using size,
      by simpa only [count,n,H,C] using lookup e⟩
  obtain ⟨same, charges, seeds⟩ := roundedForestTrialsWithChargeWork_spec links weights fractional.1.1
    scale (earlyTrialCount V height) seed W H C B forestRead access seedWork
  have roundedWork : rounded.2.1+2 ≤ earlyRoundingChargeWordBudget n links.card scale fuel W height
      (earlyTrialCount V height) P.length := by
    change rounded.2.1 ≤ _ at charges
    have cap := Nat.log2_le_self scale
    refine Nat.add_le_add_right (charges.trans ?_) 2
    dsimp only [C, H]
    gcongr
  have solver : fractional.2+5 ≤ earlyWeightedHistoryWordBudget n priced.card scale fuel W P.length := by
    change fractional.2 ≤ _ at chargeWork
    rw [count] at chargeWork
    exact Nat.add_le_add_right chargeWork _
  refine ⟨?_, Nat.zero_le _, ?_⟩
  · let priorCost := networkWeightWithDistanceWork (height := height) read
    let priorWeights := forestWeightWithDistanceWork (height := height) read
    let prior := weightedNetworkRunWithHistoryWork keys.val keys.property priced priorCost (fun _ => (0,1)) scale fuel demands
    let oldRead (e : ForestNetworkVertex V height × ForestNetworkVertex V height) := (prior.1.1 e).1
    let newRead (e : ForestNetworkVertex V height × ForestNetworkVertex V height) := (fractional.1.1 e).1
    have priorNetwork (e : ForestNetworkVertex V height × ForestNetworkVertex V height) : (priorCost e).2 ≤ B₀ :=
      readWork (heightForestLabel (ofLex e.1).2,heightForestLabel (ofLex e.2).2)
    have priorForest (e : HeightForestVertex V height × HeightForestVertex V height) : (priorWeights e).2 ≤ B₀ :=
      readWork (heightForestLabel e.1,heightForestLabel e.2)
    have priorCuts := (weightedNetworkRunWithHistoryWork_spec keys.val keys.property complete priced priorCost
      (fun _ => (0,1)) scale fuel B₀ 0 1 demands priorNetwork (fun _ => le_rfl) (fun _ => le_rfl)).1
    have matchingCost : (fun e => (cost e).1) = fun e => (priorCost e).1 :=
      funext (fun e => (networkReads e).1)
    rw [matchingCost] at cutValues
    have matchingRead : newRead = oldRead := congrArg Prod.fst (cutValues.trans priorCuts.symm)
    have matchingWeight : (fun e => (weights e).1) = fun e => (priorWeights e).1 :=
      funext (fun e => (forestReads e).1)
    let plain := fun i => forestRoundingSampleValues scale (seed i)
    have resultGraph := (congrArg Prod.fst
      (roundedForestTrialsWithSeedWork_spec links weights newRead scale _ seed B seedWork).1).trans
        (roundedForestTrialsWithWork_spec links weights newRead scale _ W forestRead plain).1
    have priorGraph := (congrArg Prod.fst
      (roundedForestTrialsWithSeedWork_spec links priorWeights oldRead scale _ seed B seedWork).1).trans
        (roundedForestTrialsWithWork_spec links priorWeights oldRead scale _ B₀ priorForest plain).1
    have sameValues : roundedForestTrialsFromWeights links (fun e => (weights e).1) newRead
        scale (earlyTrialCount V height) plain = roundedForestTrialsFromWeights links
        (fun e => (priorWeights e).1) oldRead scale (earlyTrialCount V height) plain := by
      rw [matchingWeight,matchingRead]
    change rounded.1 = (roundedForestTrialsWithSeedWork links priorWeights
      (fun e => ((weightedNetworkRunWithHistoryWork keys.val keys.property priced priorCost
        (fun _ => (0,1)) scale fuel (P.map (requestOnFreeForest free))).1.1 e).1)
      scale (earlyTrialCount V height) seed).1
    rw [← requestsEq]
    exact same.trans (resultGraph.trans (sameValues.trans priorGraph.symm))
  · change fractional.2+rounded.2.1+rounded.2.2+7+requests.2 ≤
      earlyWeightedHistoryWordBudget n priced.card scale fuel W P.length +
        earlyRoundingChargeWordBudget n links.card scale fuel W height (earlyTrialCount V height) P.length +
        earlyTrialCount V height*(links.card*((scale.log2+1)*((height+2)*B))) + requests.2
    change rounded.2.2 ≤ _ at seeds
    omega

private abbrev EarlyMetricReplay (V : Type*) (height : ℕ) :=
  (List (V × V) → Arcs (HeightForestVertex V height) × ℕ × ℕ) → List (V × V) → Arcs V × ℕ × ℕ

private theorem earlyMetricWithPreparedRequestsWork_sub {height : ℕ} (keys : ForestPairKeys V height)
    (links : Arcs (HeightForestVertex V height))
    (weights : ForestMetricWeights V height) (priced : Arcs (ForestNetworkVertex V height))
    (scale fuel : ℕ) (seed : ForestTrialArrayWithSeedWork V height scale (earlyTrialCount V height))
    (requests : ForestRequestRows V height) :
    (earlyMetricWithPreparedRequestsWork keys links weights priced scale fuel seed requests).1 ⊆ links :=
  roundedForestTrialsWithChargeWork_sub links weights.1 _ scale _ seed

@[inline] private def prepareEarlyDistanceTableForSeedFromWeightsWithRequestsWorkUsing (G : Arcs V) (height : ℕ)
    (keys : ForestPairKeys V height)
    (table : List ((V × V) × ℕ) × ℕ) (rows : table.1 = (distanceTableWithSearchWork G).1)
    (template : Arcs (HeightForestVertex V height) × ℕ) (exactForest : template.1 = heightForest G height)
    (plan : ForestWeightPlan V height)
    (matchesPlan : plan = prepareForestWeights template.1 (forestWeightWithDistanceWork (readDistanceRow table.1)))
    (readWeights : (V × V → ℕ × ℕ) → ForestMetricWeights V height)
    (requests : Arcs (ForestNetworkVertex V height) → List (V × V) → ForestRequestRows V height)
    (replay : EarlyMetricReplay V height) : SteinerSeedPreparationWithSeedWork G height :=
  prepareEarlyWithPlan (SeedAt := fun s => ForestTrialArrayWithSeedWork V height s (earlyTrialCount V height))
    G height table rows template exactForest plan matchesPlan
    (fun links query priced free scale fuel seed =>
      let weights := readWeights query
      replay
        (fun P => earlyMetricWithPreparedRequestsWork keys links weights priced scale fuel seed (requests free P)))

private theorem prepareEarlyDistanceTableForSeedFromWeightsWithRequestsWorkUsing_spec (G : Arcs V) (height : ℕ)
    (keys : ForestPairKeys V height) (complete : ∀ e, e ∈ keys.val)
    (table : List ((V × V) × ℕ) × ℕ) (rows : table.1 = (distanceTableWithSearchWork G).1)
    (template : Arcs (HeightForestVertex V height) × ℕ) (exactForest : template.1 = heightForest G height)
    (plan : ForestWeightPlan V height)
    (matchesPlan : plan = prepareForestWeights template.1 (forestWeightWithDistanceWork (readDistanceRow table.1)))
    (readWeights : (V × V → ℕ × ℕ) → ForestMetricWeights V height)
    (W : ℕ) (weightsMatch : MetricWeightReadsMatch (readDistanceRow table.1) (readWeights (readDistanceRow table.1)) W)
    (requests : Arcs (ForestNetworkVertex V height) → List (V × V) → ForestRequestRows V height)
    (requestBound : ℕ → ℕ) (mono : Monotone requestBound)
    (requestSpec : ∀ P, (requests plan.1.2 P).1 = P.map (requestOnFreeForest plan.1.2) ∧
      (requests plan.1.2 P).2 ≤ requestBound P.length)
    (replay : EarlyMetricReplay V height) (extra : ℕ → ℕ)
    (replaySpec : ∀ evaluate D K,
      (∀ P ∈ D.inits, (evaluate P).1 ⊆ template.1) → (∀ P ∈ D.inits, (evaluate P).2.2 ≤ K) →
      let out := replay evaluate D
      let old := earlyRoundedGraphWithSeedReadsFromMetric G height evaluate D
      out.1 = old.1 ∧ out.2.1 ≤ old.2.1 ∧ out.2.2 ≤ (D.length+1)*K+extra D.length) :
    let prepared := prepareEarlyDistanceTableForSeedFromWeightsWithRequestsWorkUsing G height keys
      table rows template exactForest plan matchesPlan readWeights requests replay
    let old := prepareEarlyDistanceTableForSeedFromWeightsWithHistoryWork G height keys
      table rows template exactForest plan matchesPlan
    prepared.1 = old.1 ∧ prepared.2.2 = old.2.2 ∧
    ∀ (samples : ForestTrialArrayWithSeedWork V height (forestScale G height) (earlyTrialCount V height))
      (B : ℕ), (∀ i, forestSampleWorkBound (samples i) B) → ∀ (D : List (V × V)),
      let result := prepared.2.1 samples D
      let prior := old.2.1 samples D
      let n := Fintype.card (ForestNetworkVertex V height)
      let scale := plan.2.1.1
      let fuel := plan.2.1.2
      result.1 = prior.1 ∧ result.2.1 ≤ prior.2.1 ∧
      result.2.2 ≤ (D.length+1) * (earlyWeightedHistoryWordBudget n plan.1.1.card scale fuel W D.length +
        earlyRoundingChargeWordBudget n template.1.card scale fuel W height (earlyTrialCount V height) D.length +
        earlyRoundingSeedReadBound G height * B + requestBound D.length) + extra D.length := by
  intro prepared old
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [prepared, old, prepareEarlyDistanceTableForSeedFromWeightsWithRequestsWorkUsing,
      prepareEarlyDistanceTableForSeedFromWeightsWithHistoryWork, prepareEarlyWithPlan]
  · dsimp only [prepared, old, prepareEarlyDistanceTableForSeedFromWeightsWithRequestsWorkUsing,
      prepareEarlyDistanceTableForSeedFromWeightsWithHistoryWork, prepareEarlyWithPlan]
  intro samples B cap D
  let net := Fintype.card (ForestNetworkVertex V height)
  let read := readDistanceRow table.1
  let weights := readWeights read
  let priced := plan.1.1
  let scale := plan.2.1.1
  let fuel := plan.2.1.2
  have exactScale : scale = forestScale G height := old.1.property
  let seed : ForestTrialArrayWithSeedWork V height scale (earlyTrialCount V height) :=
    cast (congrArg (fun s => ForestTrialArrayWithSeedWork V height s (earlyTrialCount V height)) exactScale.symm) samples
  let newMetric := fun P => earlyMetricWithPreparedRequestsWork keys template.1 weights priced scale fuel seed
    (requests plan.1.2 P)
  let oldMetric := earlyMetricWithPreparedHistoryWork keys template.1 read priced plan.1.2 scale fuel seed
  let ready := earlyWeightedHistoryWordBudget net priced.card scale fuel W D.length
  let rounding := earlyRoundingChargeWordBudget net template.1.card scale fuel W height (earlyTrialCount V height) D.length
  let seedReads := earlyTrialCount V height*(template.1.card*((scale.log2+1)*((height+2)*B)))
  have readBound (d : V × V) : (read d).2 ≤ (Fintype.card V)^2 := readDistanceRow_work_bound G table.1 rows d
  obtain ⟨seedCap, _⟩ := castForestTrialWork_spec exactScale.symm samples B cap
  have metric (P : List (V × V)) := earlyMetricWithPreparedRequestsWork_spec keys complete
    template.1 read priced plan.1.2 scale fuel _ W readBound weights weightsMatch.1 weightsMatch.2
    seed B seedCap P _ (requestSpec P).1
  have work (P : List (V × V)) (on : P ∈ D.inits) :
      (newMetric P).2.2 ≤ ready+rounding+seedReads+requestBound D.length := by
    have short := ((List.mem_inits _ _).mp on).length_le
    exact (metric P).2.2.trans (Nat.add_le_add (Nat.add_le_add_right (Nat.add_le_add
      (earlyWeightedHistoryWordBudget_le le_rfl le_rfl le_rfl le_rfl le_rfl short)
      (earlyRoundingChargeWordBudget_le le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl short)) _)
      ((requestSpec P).2.trans (mono short)))
  have readySeed : seedReads = earlyRoundingSeedReadBound G height * B := by
    unfold seedReads earlyRoundingSeedReadBound
    rw [exactForest, exactScale]
    ring
  obtain ⟨graph,search,_⟩ := earlyRoundedGraphWithSeedReadsFromMetric_compare G height newMetric oldMetric D
    _ (fun P _ => ⟨(metric P).1,(metric P).2.1⟩) work
  have supported (P : List (V × V)) : (newMetric P).1 ⊆ template.1 :=
    earlyMetricWithPreparedRequestsWork_sub keys template.1 weights priced scale fuel seed (requests plan.1.2 P)
  obtain ⟨updated,updatedSearch,total⟩ := replaySpec newMetric D _ (fun P _ => supported P) work
  change (replay newMetric D).1 = (earlyRoundedGraphWithSeedReadsFromMetric G height oldMetric D).1 ∧
    (replay newMetric D).2.1 ≤ (earlyRoundedGraphWithSeedReadsFromMetric G height oldMetric D).2.1 ∧
    (replay newMetric D).2.2 ≤
      (D.length+1) * (ready+rounding+earlyRoundingSeedReadBound G height*B+requestBound D.length) + extra D.length
  exact ⟨updated.trans graph,updatedSearch.trans search,readySeed ▸ total⟩

@[inline] private def prepareEarlyDistanceTableForSeedFromWeightsWithRequestsWork (G : Arcs V) (height : ℕ)
    (keys : ForestPairKeys V height)
    (table : List ((V × V) × ℕ) × ℕ) (rows : table.1 = (distanceTableWithSearchWork G).1)
    (template : Arcs (HeightForestVertex V height) × ℕ) (exactForest : template.1 = heightForest G height)
    (plan : ForestWeightPlan V height)
    (matchesPlan : plan = prepareForestWeights template.1 (forestWeightWithDistanceWork (readDistanceRow table.1)))
    (readWeights : (V × V → ℕ × ℕ) → ForestMetricWeights V height)
    (requests : Arcs (ForestNetworkVertex V height) → List (V × V) → ForestRequestRows V height) :
    SteinerSeedPreparationWithSeedWork G height :=
  prepareEarlyDistanceTableForSeedFromWeightsWithRequestsWorkUsing G height keys table rows template exactForest plan
    matchesPlan readWeights requests (earlyRoundedGraphWithSeedReadsFromMetric G height)

private theorem prepareEarlyDistanceTableForSeedFromWeightsWithRequestsWork_spec (G : Arcs V) (height : ℕ)
    (keys : ForestPairKeys V height) (complete : ∀ e, e ∈ keys.val)
    (table : List ((V × V) × ℕ) × ℕ) (rows : table.1 = (distanceTableWithSearchWork G).1)
    (template : Arcs (HeightForestVertex V height) × ℕ) (exactForest : template.1 = heightForest G height)
    (plan : ForestWeightPlan V height)
    (matchesPlan : plan = prepareForestWeights template.1 (forestWeightWithDistanceWork (readDistanceRow table.1)))
    (readWeights : (V × V → ℕ × ℕ) → ForestMetricWeights V height)
    (W : ℕ) (weightsMatch : MetricWeightReadsMatch (readDistanceRow table.1) (readWeights (readDistanceRow table.1)) W)
    (requests : Arcs (ForestNetworkVertex V height) → List (V × V) → ForestRequestRows V height)
    (requestBound : ℕ → ℕ) (mono : Monotone requestBound)
    (requestSpec : ∀ P, (requests plan.1.2 P).1 = P.map (requestOnFreeForest plan.1.2) ∧
      (requests plan.1.2 P).2 ≤ requestBound P.length) :
    let prepared := prepareEarlyDistanceTableForSeedFromWeightsWithRequestsWork G height keys
      table rows template exactForest plan matchesPlan readWeights requests
    let old := prepareEarlyDistanceTableForSeedFromWeightsWithHistoryWork G height keys
      table rows template exactForest plan matchesPlan
    prepared.1 = old.1 ∧ prepared.2.2 = old.2.2 ∧
    ∀ (samples : ForestTrialArrayWithSeedWork V height (forestScale G height) (earlyTrialCount V height))
      (B : ℕ), (∀ i, forestSampleWorkBound (samples i) B) → ∀ (D : List (V × V)),
      let result := prepared.2.1 samples D
      let prior := old.2.1 samples D
      let n := Fintype.card (ForestNetworkVertex V height)
      let scale := plan.2.1.1
      let fuel := plan.2.1.2
      result.1 = prior.1 ∧ result.2.1 ≤ prior.2.1 ∧
      result.2.2 ≤ (D.length+1) * (earlyWeightedHistoryWordBudget n plan.1.1.card scale fuel W D.length +
        earlyRoundingChargeWordBudget n template.1.card scale fuel W height (earlyTrialCount V height) D.length +
        earlyRoundingSeedReadBound G height * B + requestBound D.length) := by
  obtain ⟨scale,setup,evaluate⟩ := prepareEarlyDistanceTableForSeedFromWeightsWithRequestsWorkUsing_spec
    G height keys complete table rows template exactForest plan matchesPlan readWeights W weightsMatch
    requests requestBound mono requestSpec (earlyRoundedGraphWithSeedReadsFromMetric G height) (fun _ => 0)
    (fun metric D K _ cap => ⟨rfl,le_rfl,(earlyRoundedGraphWithSeedReadsFromMetric_spec G height metric D K cap).2.trans
      (Nat.le_add_right _ _)⟩)
  refine ⟨scale,setup,fun samples B cap D => ?_⟩
  dsimp only [prepareEarlyDistanceTableForSeedFromWeightsWithRequestsWork]
  simpa only [Nat.add_zero] using evaluate samples B cap D

/-- Keep the same weighted plan and meter the charge reads during each
metric prefix's forest rounding. -/
def prepareEarlyDistanceTableForSeedFromWeightsWithRoundingChargeWork (G : Arcs V) (height : ℕ)
    (keys : ForestPairKeys V height)
    (table : List ((V × V) × ℕ) × ℕ) (rows : table.1 = (distanceTableWithSearchWork G).1)
    (template : Arcs (HeightForestVertex V height) × ℕ) (exactForest : template.1 = heightForest G height)
    (plan : ForestWeightPlan V height)
    (matchesPlan : plan = prepareForestWeights template.1 (forestWeightWithDistanceWork (readDistanceRow table.1))) :
    SteinerSeedPreparationWithSeedWork G height :=
  prepareEarlyDistanceTableForSeedFromWeightsWithRequestsWork G height keys table rows template exactForest plan
    matchesPlan distanceOnlyMetricWeights (fun free P => (P.map (requestOnFreeForest free),0))

theorem prepareEarlyDistanceTableForSeedFromWeightsWithRoundingChargeWork_spec (G : Arcs V) (height : ℕ)
    (keys : ForestPairKeys V height) (complete : ∀ e, e ∈ keys.val)
    (table : List ((V × V) × ℕ) × ℕ) (rows : table.1 = (distanceTableWithSearchWork G).1)
    (template : Arcs (HeightForestVertex V height) × ℕ) (exactForest : template.1 = heightForest G height)
    (plan : ForestWeightPlan V height)
    (matchesPlan : plan = prepareForestWeights template.1 (forestWeightWithDistanceWork (readDistanceRow table.1))) :
    let prepared := prepareEarlyDistanceTableForSeedFromWeightsWithRoundingChargeWork G height keys
      table rows template exactForest plan matchesPlan
    let old := prepareEarlyDistanceTableForSeedFromWeightsWithHistoryWork G height keys
      table rows template exactForest plan matchesPlan
    prepared.1 = old.1 ∧ prepared.2.2 = old.2.2 ∧
    ∀ (samples : ForestTrialArrayWithSeedWork V height (forestScale G height) (earlyTrialCount V height))
      (B : ℕ), (∀ i, forestSampleWorkBound (samples i) B) → ∀ (D : List (V × V)),
      let result := prepared.2.1 samples D
      let prior := old.2.1 samples D
      let n := Fintype.card (ForestNetworkVertex V height)
      let w := (Fintype.card V)^2
      let scale := plan.2.1.1
      let fuel := plan.2.1.2
      result.1 = prior.1 ∧ result.2.1 ≤ prior.2.1 ∧
      result.2.2 ≤ (D.length+1) * (earlyWeightedHistoryWordBudget n plan.1.1.card scale fuel w D.length +
        earlyRoundingChargeWordBudget n template.1.card scale fuel w height (earlyTrialCount V height) D.length +
        earlyRoundingSeedReadBound G height * B) := by
  obtain ⟨scale,setup,evaluate⟩ := prepareEarlyDistanceTableForSeedFromWeightsWithRequestsWork_spec
    G height keys complete table rows template exactForest plan matchesPlan
    distanceOnlyMetricWeights _ (distanceOnlyMetricWeights_match _ _ (readDistanceRow_work_bound G table.1 rows))
    (fun free P => (P.map (requestOnFreeForest free),0)) (fun _ => 0)
    (fun _ _ _ => le_rfl) (fun _ => ⟨rfl,le_rfl⟩)
  refine ⟨scale,setup,fun samples B cap D => ?_⟩
  dsimp only [prepareEarlyDistanceTableForSeedFromWeightsWithRoundingChargeWork]
  simpa only [Nat.add_zero] using evaluate samples B cap D

@[inline] private def meteredForestRequests {height : ℕ}
    (vertices : List (HeightForestVertex V height)) (distinct : vertices.Nodup)
    (free : Arcs (ForestNetworkVertex V height)) (P : List (V × V)) : ForestRequestRows V height :=
  let out := forestRequestsWithWordWork vertices distinct free P
  (out.1,out.2+7)

/-- Build the exact source and sink attachments with supplied forest rows
before running the weighted separator at each metric prefix. -/
def prepareEarlyDistanceTableForSeedFromWeightsWithAttachmentWork (G : Arcs V) (height : ℕ)
    (keys : ForestPairKeys V height) (vertices : List (HeightForestVertex V height)) (distinct : vertices.Nodup)
    (table : List ((V × V) × ℕ) × ℕ) (rows : table.1 = (distanceTableWithSearchWork G).1)
    (template : Arcs (HeightForestVertex V height) × ℕ) (exactForest : template.1 = heightForest G height)
    (plan : ForestWeightPlan V height)
    (matchesPlan : plan = prepareForestWeights template.1 (forestWeightWithDistanceWork (readDistanceRow table.1))) :
    SteinerSeedPreparationWithSeedWork G height :=
  prepareEarlyDistanceTableForSeedFromWeightsWithRequestsWork G height keys table rows template exactForest plan
    matchesPlan distanceOnlyMetricWeights (meteredForestRequests vertices distinct)

def earlyAttachmentWordBudget (height vertices free p : ℕ) : ℕ :=
  p * (forestRequestWordBudget height vertices free + 9) + 10

theorem earlyAttachmentWordBudget_le {height vertices vertices' free free' p p' : ℕ}
    (rows : vertices ≤ vertices') (edges : free ≤ free') (requests : p ≤ p') :
    earlyAttachmentWordBudget height vertices free p ≤ earlyAttachmentWordBudget height vertices' free' p' := by
  unfold earlyAttachmentWordBudget
  exact Nat.add_le_add_right (Nat.mul_le_mul requests (Nat.add_le_add_right (forestRequestWordBudget_le rows edges) 9)) 10

private theorem meteredForestRequests_spec {height : ℕ}
    (vertices : List (HeightForestVertex V height)) (distinct : vertices.Nodup) (all : ∀ v, v ∈ vertices)
    (free : Arcs (ForestNetworkVertex V height)) (P : List (V × V)) :
    let out := meteredForestRequests vertices distinct free P
    out.1 = P.map (requestOnFreeForest free) ∧
      out.2 ≤ earlyAttachmentWordBudget height vertices.length free.card P.length := by
  obtain ⟨exactRows, work⟩ := forestRequestsWithWordWork_spec vertices distinct all free P
  exact ⟨exactRows,Nat.add_le_add_right work 7⟩

theorem prepareEarlyDistanceTableForSeedFromWeightsWithAttachmentWork_spec (G : Arcs V) (height : ℕ)
    (keys : ForestPairKeys V height) (complete : ∀ e, e ∈ keys.val)
    (vertices : List (HeightForestVertex V height)) (distinct : vertices.Nodup) (all : ∀ v, v ∈ vertices)
    (table : List ((V × V) × ℕ) × ℕ) (rows : table.1 = (distanceTableWithSearchWork G).1)
    (template : Arcs (HeightForestVertex V height) × ℕ) (exactForest : template.1 = heightForest G height)
    (plan : ForestWeightPlan V height)
    (matchesPlan : plan = prepareForestWeights template.1 (forestWeightWithDistanceWork (readDistanceRow table.1))) :
    let prepared := prepareEarlyDistanceTableForSeedFromWeightsWithAttachmentWork G height keys vertices distinct
      table rows template exactForest plan matchesPlan
    let old := prepareEarlyDistanceTableForSeedFromWeightsWithHistoryWork G height keys table rows template exactForest
      plan matchesPlan
    prepared.1 = old.1 ∧ prepared.2.2 = old.2.2 ∧
    ∀ (samples : ForestTrialArrayWithSeedWork V height (forestScale G height) (earlyTrialCount V height))
      (B : ℕ), (∀ i, forestSampleWorkBound (samples i) B) → ∀ (D : List (V × V)),
      let result := prepared.2.1 samples D
      let prior := old.2.1 samples D
      let n := Fintype.card (ForestNetworkVertex V height)
      let w := (Fintype.card V)^2
      let scale := plan.2.1.1
      let fuel := plan.2.1.2
      result.1 = prior.1 ∧ result.2.1 ≤ prior.2.1 ∧
      result.2.2 ≤ (D.length+1) * (earlyWeightedHistoryWordBudget n plan.1.1.card scale fuel w D.length +
        earlyRoundingChargeWordBudget n template.1.card scale fuel w height (earlyTrialCount V height) D.length +
        earlyRoundingSeedReadBound G height * B + earlyAttachmentWordBudget height vertices.length plan.1.2.card D.length) := by
  exact prepareEarlyDistanceTableForSeedFromWeightsWithRequestsWork_spec G height keys complete table rows
    template exactForest plan matchesPlan
    distanceOnlyMetricWeights _ (distanceOnlyMetricWeights_match _ _ (readDistanceRow_work_bound G table.1 rows))
    _ _ (fun _ _ le => earlyAttachmentWordBudget_le le_rfl le_rfl le)
    (meteredForestRequests_spec vertices distinct all plan.1.2)

/-- Measure the terminal-label and table reads used by the separator and
rounding in addition to the request and charge work. -/
def prepareEarlyDistanceTableForSeedFromWeightsWithMetricLabelWork (G : Arcs V) (height : ℕ)
    (keys : ForestPairKeys V height) (vertices : List (HeightForestVertex V height)) (distinct : vertices.Nodup)
    (table : List ((V × V) × ℕ) × ℕ) (rows : table.1 = (distanceTableWithSearchWork G).1)
    (template : Arcs (HeightForestVertex V height) × ℕ) (exactForest : template.1 = heightForest G height)
    (plan : ForestWeightPlan V height)
    (matchesPlan : plan = prepareForestWeights template.1 (forestWeightWithDistanceWork (readDistanceRow table.1))) :
    SteinerSeedPreparationWithSeedWork G height :=
  prepareEarlyDistanceTableForSeedFromWeightsWithRequestsWork G height keys table rows template exactForest plan
    matchesPlan labelMetricWeights (meteredForestRequests vertices distinct)

theorem prepareEarlyDistanceTableForSeedFromWeightsWithMetricLabelWork_spec (G : Arcs V) (height : ℕ)
    (keys : ForestPairKeys V height) (complete : ∀ e, e ∈ keys.val)
    (vertices : List (HeightForestVertex V height)) (distinct : vertices.Nodup) (all : ∀ v, v ∈ vertices)
    (table : List ((V × V) × ℕ) × ℕ) (rows : table.1 = (distanceTableWithSearchWork G).1)
    (template : Arcs (HeightForestVertex V height) × ℕ) (exactForest : template.1 = heightForest G height)
    (plan : ForestWeightPlan V height)
    (matchesPlan : plan = prepareForestWeights template.1 (forestWeightWithDistanceWork (readDistanceRow table.1))) :
    let prepared := prepareEarlyDistanceTableForSeedFromWeightsWithMetricLabelWork G height keys vertices distinct
      table rows template exactForest plan matchesPlan
    let old := prepareEarlyDistanceTableForSeedFromWeightsWithHistoryWork G height keys table rows template exactForest
      plan matchesPlan
    prepared.1 = old.1 ∧ prepared.2.2 = old.2.2 ∧
    ∀ (samples : ForestTrialArrayWithSeedWork V height (forestScale G height) (earlyTrialCount V height))
      (B : ℕ), (∀ i, forestSampleWorkBound (samples i) B) → ∀ (D : List (V × V)),
      let result := prepared.2.1 samples D
      let prior := old.2.1 samples D
      let n := Fintype.card (ForestNetworkVertex V height)
      let W := forestMetricLabelWordBudget height ((Fintype.card V)^2)
      let scale := plan.2.1.1
      let fuel := plan.2.1.2
      result.1 = prior.1 ∧ result.2.1 ≤ prior.2.1 ∧
      result.2.2 ≤ (D.length+1) * (earlyWeightedHistoryWordBudget n plan.1.1.card scale fuel W D.length +
        earlyRoundingChargeWordBudget n template.1.card scale fuel W height (earlyTrialCount V height) D.length +
        earlyRoundingSeedReadBound G height * B + earlyAttachmentWordBudget height vertices.length plan.1.2.card D.length) := by
  exact prepareEarlyDistanceTableForSeedFromWeightsWithRequestsWork_spec G height keys complete table rows
    template exactForest plan matchesPlan
    labelMetricWeights _ (labelMetricWeights_spec _ _ (readDistanceRow_work_bound G table.1 rows))
    _ _ (fun _ _ le => earlyAttachmentWordBudget_le le_rfl le_rfl le)
    (meteredForestRequests_spec vertices distinct all plan.1.2)

/-- One expansion allowance for each prefix row and one for the final forest. -/
def earlySteinerExpansionWordBudget (n m h rows p : ℕ) : ℕ :=
  let E := expandForestLinksFromRowsWordBudget n m h rows rows
  (p+1)*(E+8)+E+6

theorem earlySteinerExpansionWordBudget_le {n m m' h r r' p p' : ℕ}
    (arcs : m ≤ m') (rows : r ≤ r') (prefixes : p ≤ p') :
    earlySteinerExpansionWordBudget n m h r p ≤ earlySteinerExpansionWordBudget n m' h r' p' := by
  unfold earlySteinerExpansionWordBudget
  dsimp only
  have cost := expandForestLinksFromRowsWordBudget_le (n := n) (h := h) arcs rows rows
  gcongr

/-- Reuse the supplied original arc list and forest template when checking
and returning the expanded early graph. -/
def prepareEarlyDistanceTableForSeedFromWeightsWithMetricExpansionWork (G : Arcs V) (height : ℕ)
    (arcs : List (V × V)) (n : ℕ) (size : n = Fintype.card V)
    (forestRows : List (HeightForestVertex V height × HeightForestVertex V height))
    (keys : ForestPairKeys V height) (vertices : List (HeightForestVertex V height)) (distinct : vertices.Nodup)
    (table : List ((V × V) × ℕ) × ℕ) (rows : table.1 = (distanceTableWithSearchWork G).1)
    (template : Arcs (HeightForestVertex V height) × ℕ) (exactForest : template.1 = heightForest G height)
    (plan : ForestWeightPlan V height)
    (matchesPlan : plan = prepareForestWeights template.1 (forestWeightWithDistanceWork (readDistanceRow table.1))) :
    SteinerSeedPreparationWithSeedWork G height :=
  prepareEarlyDistanceTableForSeedFromWeightsWithRequestsWorkUsing G height keys table rows template exactForest plan
    matchesPlan labelMetricWeights (meteredForestRequests vertices distinct)
    (fun metric => earlyRoundedGraphWithSeedReadsAndExpansionFromMetric G n height metric
      (fun bought => expandForestLinksFromRowsWithWordWork arcs n size bought forestRows))

theorem prepareEarlyDistanceTableForSeedFromWeightsWithMetricExpansionWork_spec (G : Arcs V) (height : ℕ)
    (arcs : List (V × V)) (same : arcs.toFinset = G) (n : ℕ) (size : n = Fintype.card V)
    (forestRows : List (HeightForestVertex V height × HeightForestVertex V height))
    (keys : ForestPairKeys V height) (complete : ∀ e, e ∈ keys.val)
    (vertices : List (HeightForestVertex V height)) (distinct : vertices.Nodup) (all : ∀ v, v ∈ vertices)
    (table : List ((V × V) × ℕ) × ℕ) (rows : table.1 = (distanceTableWithSearchWork G).1)
    (template : Arcs (HeightForestVertex V height) × ℕ) (exactForest : template.1 = heightForest G height)
    (templateRows : forestRows.toFinset = template.1)
    (plan : ForestWeightPlan V height)
    (matchesPlan : plan = prepareForestWeights template.1 (forestWeightWithDistanceWork (readDistanceRow table.1))) :
    let prepared := prepareEarlyDistanceTableForSeedFromWeightsWithMetricExpansionWork G height arcs n size forestRows keys vertices distinct
      table rows template exactForest plan matchesPlan
    let old := prepareEarlyDistanceTableForSeedFromWeightsWithHistoryWork G height keys table rows template exactForest
      plan matchesPlan
    prepared.1 = old.1 ∧ prepared.2.2 = old.2.2 ∧
    ∀ (samples : ForestTrialArrayWithSeedWork V height (forestScale G height) (earlyTrialCount V height))
      (B : ℕ), (∀ i, forestSampleWorkBound (samples i) B) → ∀ (D : List (V × V)),
      let result := prepared.2.1 samples D
      let prior := old.2.1 samples D
      let N := Fintype.card (ForestNetworkVertex V height)
      let W := forestMetricLabelWordBudget height ((Fintype.card V)^2)
      let scale := plan.2.1.1
      let fuel := plan.2.1.2
      result.1 = prior.1 ∧ result.2.1 ≤ prior.2.1 ∧
      result.2.2 ≤ (D.length+1) * (earlyWeightedHistoryWordBudget N plan.1.1.card scale fuel W D.length +
        earlyRoundingChargeWordBudget N template.1.card scale fuel W height (earlyTrialCount V height) D.length +
        earlyRoundingSeedReadBound G height * B + earlyAttachmentWordBudget height vertices.length plan.1.2.card D.length) +
          earlySteinerExpansionWordBudget n arcs.length height forestRows.length D.length := by
  let expand := fun bought => expandForestLinksFromRowsWithWordWork arcs n size bought forestRows
  let limit := expandForestLinksFromRowsWordBudget n arcs.length height forestRows.length forestRows.length
  have expansion (H : Arcs (HeightForestVertex V height)) (supports : H ⊆ template.1) :
      (expand H).1 = (expandLabelledLinksWithSearchWork G heightForestLabel H).1 ∧ (expand H).2 ≤ limit := by
    have cover : H ⊆ forestRows.toFinset := templateRows.symm ▸ supports
    obtain ⟨exactGraph,work⟩ := expandForestLinksFromRowsWithWordWork_complete arcs n size H forestRows cover
    have enough := (Finset.card_le_card cover).trans (List.toFinset_card_le _)
    change (expand H).1 = _ at exactGraph
    rw [same] at exactGraph
    exact ⟨exactGraph.trans (expandLabelledLinksWithSearchWork_spec G heightForestLabel H).1.symm,
      work.trans (expandForestLinksFromRowsWordBudget_le le_rfl enough le_rfl)⟩
  apply prepareEarlyDistanceTableForSeedFromWeightsWithRequestsWorkUsing_spec G height keys complete table rows
    template exactForest plan matchesPlan labelMetricWeights _
    (labelMetricWeights_spec _ _ (readDistanceRow_work_bound G table.1 rows))
    _ _ (fun _ _ le => earlyAttachmentWordBudget_le le_rfl le_rfl le)
    (meteredForestRequests_spec vertices distinct all plan.1.2)
  intro metric D B supported bounded
  obtain ⟨graph,search,work⟩ := earlyRoundedGraphWithSeedReadsAndExpansionFromMetric_compare G n height size
    metric expand template.1 D B limit expansion supported bounded
  refine ⟨graph,search,work.trans_eq ?_⟩
  unfold earlySteinerExpansionWordBudget
  dsimp only [limit]
  ring

private def validateExpandedEarlyDemandWithWordWork (arcs : List (V × V)) (n : ℕ)
    (expanded : Arcs V) (d : V × V) : Bool × ℕ × ℕ :=
  let checked := expandedDemandMissWithWordWork arcs expanded d n
  (checked.1,0,checked.2+5)

/-- Add the reverse search and terminal test for each expanded prefix. -/
def earlySteinerExpansionAndValidationWordBudget (n m h rows p : ℕ) : ℕ :=
  earlySteinerExpansionWordBudget n m h rows p + (p+1)*(expandedDemandMissWordBudget n m m+5)

theorem earlySteinerExpansionAndValidationWordBudget_le {n m m' h r r' p p' : ℕ}
    (arcs : m ≤ m') (rows : r ≤ r') (prefixes : p ≤ p') :
    earlySteinerExpansionAndValidationWordBudget n m h r p ≤
      earlySteinerExpansionAndValidationWordBudget n m' h r' p' :=
  Nat.add_le_add (earlySteinerExpansionWordBudget_le arcs rows prefixes)
    (Nat.mul_le_mul (Nat.add_le_add_right prefixes 1)
      (Nat.add_le_add_right (expandedDemandMissWordBudget_le arcs arcs) 5))

/-- Validate each expanded early prefix with the metered reverse search
on the original arc rows. -/
def prepareEarlyDistanceTableForSeedFromWeightsWithMetricValidationWork (G : Arcs V) (height : ℕ)
    (arcs : List (V × V)) (n : ℕ) (size : n = Fintype.card V)
    (forestRows : List (HeightForestVertex V height × HeightForestVertex V height))
    (keys : ForestPairKeys V height) (vertices : List (HeightForestVertex V height)) (distinct : vertices.Nodup)
    (table : List ((V × V) × ℕ) × ℕ) (rows : table.1 = (distanceTableWithSearchWork G).1)
    (template : Arcs (HeightForestVertex V height) × ℕ) (exactForest : template.1 = heightForest G height)
    (plan : ForestWeightPlan V height)
    (matchesPlan : plan = prepareForestWeights template.1 (forestWeightWithDistanceWork (readDistanceRow table.1))) :
    SteinerSeedPreparationWithSeedWork G height :=
  prepareEarlyDistanceTableForSeedFromWeightsWithRequestsWorkUsing G height keys table rows template exactForest plan
    matchesPlan labelMetricWeights (meteredForestRequests vertices distinct)
    (fun metric => earlyRoundedGraphWithSeedReadsExpansionAndValidationFromMetric G height metric
      (fun bought => expandForestLinksFromRowsWithWordWork arcs n size bought forestRows)
      (validateExpandedEarlyDemandWithWordWork arcs n))

theorem prepareEarlyDistanceTableForSeedFromWeightsWithMetricValidationWork_spec (G : Arcs V) (height : ℕ)
    (arcs : List (V × V)) (same : arcs.toFinset = G) (n : ℕ) (size : n = Fintype.card V)
    (forestRows : List (HeightForestVertex V height × HeightForestVertex V height))
    (keys : ForestPairKeys V height) (complete : ∀ e, e ∈ keys.val)
    (vertices : List (HeightForestVertex V height)) (distinct : vertices.Nodup) (all : ∀ v, v ∈ vertices)
    (table : List ((V × V) × ℕ) × ℕ) (rows : table.1 = (distanceTableWithSearchWork G).1)
    (template : Arcs (HeightForestVertex V height) × ℕ) (exactForest : template.1 = heightForest G height)
    (templateRows : forestRows.toFinset = template.1)
    (plan : ForestWeightPlan V height)
    (matchesPlan : plan = prepareForestWeights template.1 (forestWeightWithDistanceWork (readDistanceRow table.1))) :
    let prepared := prepareEarlyDistanceTableForSeedFromWeightsWithMetricValidationWork G height arcs n size forestRows keys vertices distinct
      table rows template exactForest plan matchesPlan
    let old := prepareEarlyDistanceTableForSeedFromWeightsWithHistoryWork G height keys table rows template exactForest
      plan matchesPlan
    prepared.1 = old.1 ∧ prepared.2.2 = old.2.2 ∧
    ∀ (samples : ForestTrialArrayWithSeedWork V height (forestScale G height) (earlyTrialCount V height))
      (B : ℕ), (∀ i, forestSampleWorkBound (samples i) B) → ∀ (D : List (V × V)),
      let result := prepared.2.1 samples D
      let prior := old.2.1 samples D
      let N := Fintype.card (ForestNetworkVertex V height)
      let W := forestMetricLabelWordBudget height ((Fintype.card V)^2)
      let scale := plan.2.1.1
      let fuel := plan.2.1.2
      result.1 = prior.1 ∧ result.2.1 ≤ prior.2.1 ∧
      result.2.2 ≤ (D.length+1) * (earlyWeightedHistoryWordBudget N plan.1.1.card scale fuel W D.length +
        earlyRoundingChargeWordBudget N template.1.card scale fuel W height (earlyTrialCount V height) D.length +
        earlyRoundingSeedReadBound G height * B + earlyAttachmentWordBudget height vertices.length plan.1.2.card D.length) +
          earlySteinerExpansionAndValidationWordBudget n arcs.length height forestRows.length D.length := by
  let expand := fun bought => expandForestLinksFromRowsWithWordWork arcs n size bought forestRows
  let limit := expandForestLinksFromRowsWordBudget n arcs.length height forestRows.length forestRows.length
  have expansion (H : Arcs (HeightForestVertex V height)) (supports : H ⊆ template.1) :
      (expand H).1 = (expandLabelledLinksWithSearchWork G heightForestLabel H).1 ∧ (expand H).2 ≤ limit := by
    have cover : H ⊆ forestRows.toFinset := templateRows.symm ▸ supports
    obtain ⟨exactGraph,work⟩ := expandForestLinksFromRowsWithWordWork_complete arcs n size H forestRows cover
    have enough := (Finset.card_le_card cover).trans (List.toFinset_card_le _)
    change (expand H).1 = _ at exactGraph
    rw [same] at exactGraph
    exact ⟨exactGraph.trans (expandLabelledLinksWithSearchWork_spec G heightForestLabel H).1.symm,
      work.trans (expandForestLinksFromRowsWordBudget_le le_rfl enough le_rfl)⟩
  let validate := validateExpandedEarlyDemandWithWordWork arcs n
  let checkBudget := expandedDemandMissWordBudget n arcs.length arcs.length+5
  have checked (H : Arcs (HeightForestVertex V height)) (supports : H ⊆ template.1) (d : V × V) :
      let out := validate (expand H).1 d
      let old := reachInWithArcInspections (expand H).1 d.2 n
      out.1 = decide (d.1 ∉ old.1) ∧ out.2.1 ≤ old.2 ∧ out.2.2 ≤ checkBudget := by
    have subgraph : (expand H).1 ⊆ arcs.toFinset := by
      rw [same,(expansion H supports).1,(expandLabelledLinksWithSearchWork_spec G heightForestLabel H).1]
      exact expandLabelledLinks_sub G heightForestLabel H
    have cardBound := (Finset.card_le_card subgraph).trans (List.toFinset_card_le arcs)
    have exactCheck := expandedDemandMissWithWordWork_of_subgraph arcs (expand H).1 d subgraph
    have results : (expandedDemandMissWithWordWork arcs (expand H).1 d n).1 =
        decide (d.1 ∉ reachIn (expand H).1 d.2 n) ∧
        (expandedDemandMissWithWordWork arcs (expand H).1 d n).2 ≤
          expandedDemandMissWordBudget n arcs.length (expand H).1.card := by
      simpa only [size] using exactCheck
    refine ⟨?_,Nat.zero_le _,Nat.add_le_add_right (results.2.trans (expandedDemandMissWordBudget_le le_rfl cardBound)) 5⟩
    rw [reachInWithArcInspections_spec]
    exact results.1
  apply prepareEarlyDistanceTableForSeedFromWeightsWithRequestsWorkUsing_spec G height keys complete table rows
    template exactForest plan matchesPlan labelMetricWeights _
    (labelMetricWeights_spec _ _ (readDistanceRow_work_bound G table.1 rows))
    _ _ (fun _ _ le => earlyAttachmentWordBudget_le le_rfl le_rfl le)
    (meteredForestRequests_spec vertices distinct all plan.1.2)
  intro metric D B supported bounded
  obtain ⟨graph,search,work⟩ := earlyRoundedGraphWithSeedReadsExpansionAndValidationFromMetric_compare G n height size
    metric expand validate template.1 D B limit checkBudget expansion supported bounded checked
  refine ⟨graph,search,work.trans_eq ?_⟩
  unfold earlySteinerExpansionAndValidationWordBudget earlySteinerExpansionWordBudget
  dsimp only [limit,checkBudget]
  ring

/-- Replace the early prefix table by a metered traversal and union while
sharing the same forest metric, route expansion and validation. -/
def prepareEarlyDistanceTableForSeedFromWeightsWithMetricPrefixAssemblyWork (G : Arcs V) (height : ℕ)
    (arcs : List (V × V)) (n : ℕ) (size : n = Fintype.card V)
    (forestRows : List (HeightForestVertex V height × HeightForestVertex V height))
    (keys : ForestPairKeys V height) (vertices : List (HeightForestVertex V height)) (distinct : vertices.Nodup)
    (table : List ((V × V) × ℕ) × ℕ) (rows : table.1 = (distanceTableWithSearchWork G).1)
    (template : Arcs (HeightForestVertex V height) × ℕ) (exactForest : template.1 = heightForest G height)
    (plan : ForestWeightPlan V height)
    (matchesPlan : plan = prepareForestWeights template.1 (forestWeightWithDistanceWork (readDistanceRow table.1))) :
    SteinerSeedPreparationWithSeedWork G height :=
  prepareEarlyDistanceTableForSeedFromWeightsWithRequestsWorkUsing G height keys table rows template exactForest plan
    matchesPlan labelMetricWeights (meteredForestRequests vertices distinct)
    (fun metric => earlyRoundedGraphWithMeasuredPrefixAssembly G height metric
      (fun bought => expandForestLinksFromRowsWithWordWork arcs n size bought forestRows)
      (validateExpandedEarlyDemandWithWordWork arcs n))

theorem prepareEarlyDistanceTableForSeedFromWeightsWithMetricPrefixAssemblyWork_compare (G : Arcs V) (height : ℕ)
    (arcs : List (V × V)) (n : ℕ) (size : n = Fintype.card V)
    (forestRows : List (HeightForestVertex V height × HeightForestVertex V height))
    (keys : ForestPairKeys V height) (vertices : List (HeightForestVertex V height)) (distinct : vertices.Nodup)
    (table : List ((V × V) × ℕ) × ℕ) (rows : table.1 = (distanceTableWithSearchWork G).1)
    (template : Arcs (HeightForestVertex V height) × ℕ) (exactForest : template.1 = heightForest G height)
    (plan : ForestWeightPlan V height)
    (matchesPlan : plan = prepareForestWeights template.1 (forestWeightWithDistanceWork (readDistanceRow table.1))) :
    let fresh := prepareEarlyDistanceTableForSeedFromWeightsWithMetricPrefixAssemblyWork G height arcs n size forestRows keys vertices distinct
      table rows template exactForest plan matchesPlan
    let prior := prepareEarlyDistanceTableForSeedFromWeightsWithMetricValidationWork G height arcs n size forestRows keys vertices distinct
      table rows template exactForest plan matchesPlan
    fresh.1 = prior.1 ∧ fresh.2.2 = prior.2.2 ∧
      ∀ (samples : ForestTrialArrayWithSeedWork V height (forestScale G height) (earlyTrialCount V height)) (D : List (V × V)),
        let out := fresh.2.1 samples D
        let old := prior.2.1 samples D
        out.1 = old.1 ∧ out.2.1 = old.2.1 ∧ out.2.2 ≤ old.2.2 + earlyPrefixAssemblyWordBudget D.length template.1.card := by
  intro fresh prior
  refine ⟨rfl,rfl,fun samples D => ?_⟩
  let expand := fun bought => expandForestLinksFromRowsWithWordWork arcs n size bought forestRows
  let validate := validateExpandedEarlyDemandWithWordWork arcs n
  let scale := plan.2.1.1
  have exactScale : scale = forestScale G height := prior.1.property
  let SeedAt := fun s => ForestTrialArrayWithSeedWork V height s (earlyTrialCount V height)
  let seed : SeedAt scale := cast (congrArg SeedAt exactScale.symm) samples
  let weights := labelMetricWeights (height := height) (readDistanceRow table.1)
  let requests := meteredForestRequests vertices distinct plan.1.2
  let metric P := earlyMetricWithPreparedRequestsWork keys template.1 weights plan.1.1 scale plan.2.1.2 seed (requests P)
  have supported (P : List (V × V)) : (metric P).1 ⊆ template.1 :=
    earlyMetricWithPreparedRequestsWork_sub keys template.1 weights plan.1.1 scale plan.2.1.2 seed (requests P)
  exact earlyRoundedGraphWithMeasuredPrefixAssembly_compare G height metric expand validate D template.1 (fun P _ => supported P)

end OnlineReachabilityPreservers
