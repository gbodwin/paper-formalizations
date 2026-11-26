import OnlineReachabilityPreservers.SteinerIntervalWork
import OnlineReachabilityPreservers.SteinerCapacityWork

/-! Make the charge state explicit when evaluating the weighted separator. -/

namespace OnlineReachabilityPreservers

open Finset

/-- Read the weighted charge from an explicit reverse-chronological cut list.
The initial state supplies its value and the work needed to read it. -/
def weightedChargeHistoryWithWordWork {E : Type*} [DecidableEq E]
    (initial : E → ℕ × ℕ) (key : E) : List (Finset E) → ℕ × ℕ
  | [] =>
    let start := initial key
    (start.1, start.2 + 3)
  | cut :: rest =>
    let past := weightedChargeHistoryWithWordWork initial key rest
    let onCut := memFinsetWithWordWork key cut
    (past.1 + (if onCut.1 then 1 else 0), past.2 + onCut.2 + 8)

theorem weightedChargeHistoryWithWordWork_spec {E : Type*} [DecidableEq E]
    (initial : E → ℕ × ℕ) (key : E) (history : List (Finset E)) (q : ℕ)
    (small : ∀ cut ∈ history, cut.card ≤ q) :
    let result := weightedChargeHistoryWithWordWork initial key history
    result.1 = (history.foldr chargeWeightedCut (fun e => (initial e).1)) key ∧
      result.1 ≤ (initial key).1 + history.length ∧
      result.2 ≤ (initial key).2 + 3 + history.length * (12 * q + 14) := by
  induction history with
  | nil => simp [weightedChargeHistoryWithWordWork]
  | cons cut rest ih =>
    obtain ⟨same, value, work⟩ := ih (fun c hc => small c (List.mem_cons_of_mem _ hc))
    obtain ⟨membership, scan⟩ := memFinsetWithWordWork_spec key cut
    have scanBound : (memFinsetWithWordWork key cut).2 ≤ 12 * q + 6 :=
      scan.trans (by have head := small cut List.mem_cons_self; omega)
    simp only [weightedChargeHistoryWithWordWork, List.foldr_cons, List.length_cons]
    refine ⟨?_, ?_, ?_⟩
    · rw [same, membership, chargeWeightedCut]
      by_cases take : key ∈ cut <;> simp [take]
    · have added : (if (memFinsetWithWordWork key cut).1 then 1 else 0) ≤ 1 := by split <;> decide
      omega
    · rw [Nat.succ_mul]
      omega

/-- Compute a power of two using one metered doubling per exponent step. -/
def twoPowerWithWordWork : ℕ → ℕ × ℕ
  | 0 => (1, 3)
  | n + 1 =>
    let previous := twoPowerWithWordWork n
    (previous.1 + previous.1, previous.2 + 6)

theorem twoPowerWithWordWork_spec (n : ℕ) :
    twoPowerWithWordWork n = (2^n, 6*n+3) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [twoPowerWithWordWork, ih, Nat.mul_succ]
    apply Prod.ext
    · simp only [pow_succ, Nat.mul_two]
    · omega

/-- Compute the integer separator capacity by metered doubling. -/
def roundedWeightedCapacityWithWordWork (cost charge : ℕ) : ℕ × ℕ :=
  let doublings := twoPowerWithWordWork (charge / cost)
  let numerator := doublings.1 * (cost + charge % cost) + (cost - 1)
  (numerator / cost, doublings.2 + 14)

theorem roundedWeightedCapacityWithWordWork_spec (cost charge : ℕ) :
    let out := roundedWeightedCapacityWithWordWork cost charge
    out.1 = roundedWeightedCapacity cost charge ∧ out.2 = 6*(charge/cost)+17 := by
  rw [roundedWeightedCapacityWithWordWork]
  dsimp only
  rw [twoPowerWithWordWork_spec, roundedWeightedCapacity, weightedLoad]
  simp

/-- Keep the cut list in reverse chronological order for charge reads and
report accepted cuts in the order in which the separator returns them. -/
def weightedCoverLoopFromHistoryWithWordWork {E : Type*}
    (separate : List (Finset E) → Option (Finset E) × ℕ) :
    ℕ → List (Finset E) → (List (Finset E) × List (Finset E)) × ℕ
  | 0, history => ((history, []), 3)
  | fuel + 1, history =>
    let next := separate history
    match next.1 with
    | none => ((history, []), next.2 + 6)
    | some cut =>
      let later := weightedCoverLoopFromHistoryWithWordWork separate fuel (cut :: history)
      ((later.1.1, cut :: later.1.2), next.2 + later.2 + 10)

theorem weightedCoverLoopFromHistoryWithWordWork_spec {E : Type*} [DecidableEq E]
    (separate : List (Finset E) → Option (Finset E) × ℕ)
    (search : (E → ℕ) → Option (Finset E)) (initial : E → ℕ)
    (exactCut : ∀ history, (separate history).1 = search (history.foldr chargeWeightedCut initial))
    (H B fuel : ℕ) (history : List (Finset E)) (room : history.length + fuel ≤ H)
    (each : ∀ past, past.length ≤ H → (separate past).2 ≤ B) :
    let out := weightedCoverLoopFromHistoryWithWordWork separate fuel history
    let old := weightedCoverLoop search fuel (history.foldr chargeWeightedCut initial)
    (out.1.1.foldr chargeWeightedCut initial, out.1.2) = old ∧
      out.1.1 = out.1.2.reverse ++ history ∧
      out.1.1.length ≤ history.length + fuel ∧ out.1.2.length ≤ fuel ∧
      out.2 ≤ fuel * (B+10) + 3 := by
  induction fuel generalizing history with
  | zero => simp [weightedCoverLoopFromHistoryWithWordWork, weightedCoverLoop]
  | succ fuel ih =>
    have before := each history (by omega)
    have result := exactCut history
    cases found : (search (history.foldr chargeWeightedCut initial)) with
    | none =>
      rw [found] at result
      simp only [weightedCoverLoopFromHistoryWithWordWork, weightedCoverLoop, found, result]
      refine ⟨trivial, by simp, by omega, by simp, ?_⟩
      rw [Nat.succ_mul]
      omega
    | some cut =>
      rw [found] at result
      obtain ⟨same, historyEq, state, accepted, work⟩ := ih (cut::history) (by simpa only [List.length_cons] using (by omega :
        history.length + 1 + fuel ≤ H))
      simp only [weightedCoverLoopFromHistoryWithWordWork, weightedCoverLoop, found, result]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simpa only [List.foldr_cons] using
          congrArg (fun r : (E → ℕ) × List (Finset E) => (r.1, cut :: r.2)) same
      · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using historyEq
      · simp only [List.length_cons] at state
        omega
      · exact Nat.succ_le_succ accepted
      · rw [Nat.succ_mul]
        omega

section Capacity

variable {V : Type*} [LinearOrder V]

private def capacityFromHistoryWithWordWork (paid : Arcs V) (request : WeightedNetworkDemand V)
    (weight initial : V × V → ℕ × ℕ) (scale : ℕ)
    (history : List (Arcs V)) (key : V × V) : ℤ × ℕ :=
  let free := memFinsetWithWordWork key request.free
  if free.1 then (scale, free.2 + 9)
  else
    let priced := memFinsetWithWordWork key paid
    if priced.1 then
      let read := weight key
      let charge := weightedChargeHistoryWithWordWork initial key history
      let capacity := roundedWeightedCapacityWithWordWork read.1 charge.1
      (capacity.1, free.2 + priced.2 + read.2 + charge.2 + capacity.2 + 15)
    else (0, free.2 + priced.2 + 11)

private def weightedCapacityHistoryRowBudget (free paid cutSize weight load initial history : ℕ) : ℕ :=
  (12 * free + 6) + (12 * paid + 6) + weight +
    (initial + 3 + history * (12 * cutSize + 14)) + (6 * (load + history) + 17) + 15

private theorem capacityFromHistoryWithWordWork_spec (paid : Arcs V) (request : WeightedNetworkDemand V)
    (weight initial : V × V → ℕ × ℕ) (scale W I C Q : ℕ) (history : List (Arcs V)) (key : V × V)
    (weightWork : (weight key).2 ≤ W) (initialLoad : (initial key).1 ≤ I) (initialWork : (initial key).2 ≤ C)
    (cuts : ∀ cut ∈ history, cut.card ≤ Q) :
    let out := capacityFromHistoryWithWordWork paid request weight initial scale history key
    out.1 = weightedNetworkCapacity paid request (fun a => (weight a).1)
      (history.foldr chargeWeightedCut (fun a => (initial a).1)) scale key ∧
      out.2 ≤ weightedCapacityHistoryRowBudget request.free.card paid.card Q W I C history.length := by
  let isFree := memFinsetWithWordWork key request.free
  let isPaid := memFinsetWithWordWork key paid
  let charge := weightedChargeHistoryWithWordWork initial key history
  let rounded := roundedWeightedCapacityWithWordWork (weight key).1 charge.1
  obtain ⟨freeEq, freeWork⟩ := memFinsetWithWordWork_spec key request.free
  obtain ⟨paidEq, paidWork⟩ := memFinsetWithWordWork_spec key paid
  obtain ⟨value, load, work⟩ := weightedChargeHistoryWithWordWork_spec initial key history Q cuts
  obtain ⟨capacity, capacityWork⟩ := roundedWeightedCapacityWithWordWork_spec (weight key).1 charge.1
  have capBound : rounded.2 ≤ 6 * (I + history.length) + 17 := by
    change rounded.2 = _ at capacityWork
    change charge.1 ≤ _ at load
    have estimate := (Nat.div_le_self charge.1 (weight key).1).trans (load.trans (Nat.add_le_add_right initialLoad _))
    rw [capacityWork]
    omega
  change isFree.1 = _ at freeEq
  change isPaid.1 = _ at paidEq
  change isFree.2 ≤ _ at freeWork
  change isPaid.2 ≤ _ at paidWork
  change charge.2 ≤ _ at work
  change rounded.1 = _ at capacity
  change charge.1 = _ at value
  change (let out := if isFree.1 then ((scale : ℤ), isFree.2 + 9)
    else if isPaid.1 then ((rounded.1 : ℤ), isFree.2 + isPaid.2 + (weight key).2 + charge.2 + rounded.2 + 15)
    else (0, isFree.2 + isPaid.2 + 11)
    out.1 = _ ∧ out.2 ≤ _)
  rw [freeEq, paidEq, weightedNetworkCapacity]
  by_cases free : key ∈ request.free
  · refine ⟨by simp [free], ?_⟩
    simp only [free, decide_true, ite_true]
    unfold weightedCapacityHistoryRowBudget
    omega
  · by_cases paidKey : key ∈ paid
    · simp only [free, paidKey, decide_false, decide_true, Bool.false_eq_true, ite_false, ite_true]
      rw [capacity, value]
      exact ⟨rfl, by unfold weightedCapacityHistoryRowBudget; omega⟩
    · refine ⟨by simp [free, paidKey], ?_⟩
      simp only [free, paidKey, decide_false, Bool.false_eq_true, ite_false]
      unfold weightedCapacityHistoryRowBudget
      omega

private def capacityRowsWithWordWork {E : Type*} (read : E → ℤ × ℕ) : List E → List (E × ℤ) × ℕ
  | [] => ([], 3)
  | key :: keys =>
    let head := read key
    let tail := capacityRowsWithWordWork read keys
    ((key, head.1) :: tail.1, head.2 + tail.2 + 11)

private theorem capacityRowsWithWordWork_shape {E : Type*} (read : E → ℤ × ℕ) (keys : List E) :
    (capacityRowsWithWordWork read keys).1 = keys.map (fun key => (key, (read key).1)) := by
  induction keys with
  | nil => rfl
  | cons key keys ih => simp only [capacityRowsWithWordWork, List.map_cons, ih]

private theorem capacityRowsWithWordWork_cost {E : Type*} (read : E → ℤ × ℕ) (keys : List E) (B : ℕ)
    (each : ∀ key ∈ keys, (read key).2 ≤ B) :
    (capacityRowsWithWordWork read keys).2 ≤ keys.length * (B + 11) + 3 := by
  induction keys with
  | nil => simp [capacityRowsWithWordWork]
  | cons key keys ih =>
    have head := each key List.mem_cons_self
    have tail := ih (fun e h => each e (List.mem_cons_of_mem _ h))
    change (read key).2 + (capacityRowsWithWordWork read keys).2 + 11 ≤ (keys.length + 1) * (B + 11) + 3
    rw [Nat.add_mul, Nat.one_mul]
    omega

private def makeHistoryCapacityTable (keys : List (V × V)) (distinct : keys.Nodup) (read : V × V → ℤ × ℕ) :
    CapacityRows V × ℕ :=
  let out := capacityRowsWithWordWork read keys
  have exactKeys : out.1.map Prod.fst = keys := by
    change (capacityRowsWithWordWork read keys).1.map Prod.fst = keys
    rw [capacityRowsWithWordWork_shape, List.map_map]
    exact List.map_id' _
  (⟨out.1, exactKeys.symm ▸ distinct⟩, out.2)

variable [Fintype V]

private theorem fullCapacityKeys_length (keys : List (V × V)) (distinct : keys.Nodup) (complete : ∀ e, e ∈ keys) :
    keys.length = (Fintype.card V)^2 := by
  have allKeys : keys.toFinset = (univ : Finset (V × V)) := by
    ext e
    simp [complete]
  rw [← List.toFinset_card_of_nodup distinct, allKeys, card_univ, Fintype.card_prod, pow_two]

private def outgoingTestWithWordWork (side : Finset V) (edge : V × V) : Bool × ℕ :=
  let inside := memFinsetWithWordWork edge.1 side
  if inside.1 then
    let outside := memFinsetWithWordWork edge.2 side
    (!outside.1, inside.2 + outside.2 + 9)
  else (false, inside.2 + 6)

omit [Fintype V] in
private theorem outgoingTestWithWordWork_spec (side : Finset V) (edge : V × V) :
    let out := outgoingTestWithWordWork side edge
    out.1 = decide (edge.1 ∈ side ∧ edge.2 ∉ side) ∧ out.2 ≤ 24 * side.card + 21 := by
  obtain ⟨left, costL⟩ := memFinsetWithWordWork_spec edge.1 side
  obtain ⟨right, costR⟩ := memFinsetWithWordWork_spec edge.2 side
  unfold outgoingTestWithWordWork
  dsimp only
  rw [left]
  by_cases inside : edge.1 ∈ side
  · simp only [inside, decide_true, ite_true, true_and]
    exact ⟨by rw [right, decide_not], by omega⟩
  · simp only [inside, decide_false, Bool.false_eq_true, ite_false, false_and, true_and]
    omega

private def weightedHistoryOutgoingCutWithWordWork (paid : Arcs V) (side : Finset V) : Arcs V × ℕ :=
  filterFinsetWithWordWork (outgoingTestWithWordWork side) paid

omit [Fintype V] in
private theorem weightedHistoryOutgoingCutWithWordWork_spec (paid : Arcs V) (side : Finset V) :
    let out := weightedHistoryOutgoingCutWithWordWork paid side
    out.1 = outgoingCut paid side ∧ out.2 ≤ paid.card * (24 * side.card + 31) + 2 := by
  obtain ⟨shape, work⟩ := filterFinsetWithWordWork_spec (outgoingTestWithWordWork side) paid
  refine ⟨?_, work (24 * side.card + 21) (fun e _ => (outgoingTestWithWordWork_spec side e).2)⟩
  rw [weightedHistoryOutgoingCutWithWordWork, shape]
  ext e
  simp [outgoingCut, (outgoingTestWithWordWork_spec side e).1]

/-- Prepare the rounded capacities from explicit keys and cut history,
then use the same augmenting search and select its paid outgoing cut. -/
def weightedNetworkViolationFromHistoryWithWordWork (keys : List (V × V)) (distinct : keys.Nodup)
    (paid : Arcs V) (request : WeightedNetworkDemand V) (weight initial : V × V → ℕ × ℕ) (scale : ℕ)
    (history : List (Arcs V)) : Option (Arcs V) × ℕ :=
  let table := makeHistoryCapacityTable keys distinct (capacityFromHistoryWithWordWork paid request weight initial scale history)
  let search := findLowCapacityCutWithResidualWork (residualArcsFromCapacityRows table.1) request.source request.sink scale
  match search.1 with
  | none => (none, table.2 + search.2 + 8)
  | some side =>
    let cut := weightedHistoryOutgoingCutWithWordWork paid side
    (some cut.1, table.2 + search.2 + cut.2 + 12)

/-- Bound a weighted separator call with explicit preparation and charge
reads. This includes the previous augmentation search counts. -/
def weightedHistorySeparatorWordBudget (n m scale weight load initial history : ℕ) : ℕ :=
  weightedSeparatorWorkBound n m scale +
    n^2 * (weightedCapacityHistoryRowBudget (n^2) m (n^2) weight load initial history + 11) +
    m * (24 * n + 31) + 18

theorem weightedNetworkViolationFromHistoryWithWordWork_spec (keys : List (V × V)) (distinct : keys.Nodup)
    (complete : ∀ e, e ∈ keys) (paid : Arcs V) (request : WeightedNetworkDemand V)
    (weight initial : V × V → ℕ × ℕ) (scale W I C : ℕ) (history : List (Arcs V))
    (weightWork : ∀ e, (weight e).2 ≤ W) (initialLoad : ∀ e, (initial e).1 ≤ I)
    (initialWork : ∀ e, (initial e).2 ≤ C) :
    let out := weightedNetworkViolationFromHistoryWithWordWork keys distinct paid request weight initial scale history
    out.1 = weightedNetworkViolation paid request (fun e => (weight e).1) scale
      (history.foldr chargeWeightedCut (fun e => (initial e).1)) ∧
      out.2 ≤ weightedHistorySeparatorWordBudget (Fintype.card V) paid.card scale W I C history.length := by
  let n := Fintype.card V
  let q := n^2
  let cap := weightedNetworkCapacity paid request (fun e => (weight e).1)
    (history.foldr chargeWeightedCut (fun e => (initial e).1)) scale
  let read := capacityFromHistoryWithWordWork paid request weight initial scale history
  let table := makeHistoryCapacityTable keys distinct read
  let build := residualArcsFromCapacityRows table.1
  have cells : keys.length = q := fullCapacityKeys_length keys distinct complete
  have pairBound (A : Arcs V) : A.card ≤ q := by
    simpa only [Fintype.card_prod, pow_two, q, n] using card_le_univ A
  have readExact (e : V × V) : (read e).1 = cap e :=
    (capacityFromHistoryWithWordWork_spec paid request weight initial scale W I C q history e
      (weightWork e) (initialLoad e) (initialWork e) (fun cut _ => pairBound cut)).1
  have rowBudget (e : V × V) :
      (read e).2 ≤ weightedCapacityHistoryRowBudget q paid.card q W I C history.length := by
    refine (capacityFromHistoryWithWordWork_spec paid request weight initial scale W I C q history e
      (weightWork e) (initialLoad e) (initialWork e) (fun cut _ => pairBound cut)).2.trans ?_
    unfold weightedCapacityHistoryRowBudget
    gcongr
    exact pairBound request.free
  have shape : table.1.val = keys.map (fun e => (e, cap e)) := by
    change (capacityRowsWithWordWork read keys).1 = _
    rw [capacityRowsWithWordWork_shape]
    exact List.map_congr_left (fun e _ => congrArg (Prod.mk e) (readExact e))
  let tableBudget := q * (weightedCapacityHistoryRowBudget q paid.card q W I C history.length + 11)
  have tableWork : table.2 ≤ tableBudget + 3 := by
    change (capacityRowsWithWordWork read keys).2 ≤ _
    simpa only [cells, tableBudget] using capacityRowsWithWordWork_cost read keys _ (fun e _ => rowBudget e)
  have residualExact (flow : ArcFlow V) : build flow = (residualArcs cap flow, n^2) := by
    simpa only [cells] using residualArcsFromCapacityRows_eq_of_keys table.1 keys complete cap flow shape
  let old := findLowCapacityCutWithSearchWork cap request.source request.sink scale
  let searchBudget := scale * residualStepWorkBound n + (2 * q + n * q)
  let cutBudget := paid.card * (24 * n + 31)
  have search := findLowCapacityCutWithResidualWork_eq build cap request.source request.sink scale residualExact
  obtain ⟨answer, budget⟩ := findLowCapacityCutWithSearchWork_spec cap request.source request.sink scale
  change old.1 = _ at answer
  change old.2 ≤ searchBudget at budget
  unfold weightedNetworkViolationFromHistoryWithWordWork weightedNetworkViolation
  dsimp only
  change (let out := match findLowCapacityCutWithResidualWork build request.source request.sink scale |>.1 with
    | none => (none, table.2 + (findLowCapacityCutWithResidualWork build request.source request.sink scale).2 + 8)
    | some side =>
      let cut := weightedHistoryOutgoingCutWithWordWork paid side
      (some cut.1, table.2 + (findLowCapacityCutWithResidualWork build request.source request.sink scale).2 + cut.2 + 12)
    out.1 = (findLowCapacityCut cap request.source request.sink scale).map (outgoingCut paid) ∧ out.2 ≤ _)
  rw [search, ← answer]
  change (let out := match old.1 with
    | none => (none, table.2 + old.2 + 8)
    | some side =>
      let cut := weightedHistoryOutgoingCutWithWordWork paid side
      (some cut.1, table.2 + old.2 + cut.2 + 12)
    out.1 = old.1.map (outgoingCut paid) ∧ out.2 ≤ searchBudget + paid.card + tableBudget + cutBudget + 18)
  cases result : old.1 with
  | none =>
    refine ⟨rfl, ?_⟩
    change table.2 + old.2 + 8 ≤ _
    omega
  | some side =>
    obtain ⟨edges, work⟩ := weightedHistoryOutgoingCutWithWordWork_spec paid side
    have cutBound : (weightedHistoryOutgoingCutWithWordWork paid side).2 ≤ cutBudget + 2 := by
      exact work.trans (by unfold cutBudget; gcongr; exact card_le_univ side)
    refine ⟨congrArg some edges, ?_⟩
    change table.2 + old.2 + (weightedHistoryOutgoingCutWithWordWork paid side).2 + 12 ≤ _
    omega

/-- The separator bound is monotone in the graph size, scale, read budget,
and number of stored cuts. -/
theorem weightedHistorySeparatorWordBudget_le {n n' m m' scale scale' W W' H H' : ℕ}
    (verts : n ≤ n') (edges : m ≤ m') (scales : scale ≤ scale')
    (reads : W ≤ W') (history : H ≤ H') (I C : ℕ) :
    weightedHistorySeparatorWordBudget n m scale W I C H ≤
      weightedHistorySeparatorWordBudget n' m' scale' W' I C H' := by
  unfold weightedHistorySeparatorWordBudget weightedCapacityHistoryRowBudget
    weightedSeparatorWorkBound residualStepWorkBound
  gcongr

private theorem weightedHistorySeparatorWordBudget_mono (n m scale W I C : ℕ) :
    Monotone (weightedHistorySeparatorWordBudget n m scale W I C) := by
  intro a b hab
  exact weightedHistorySeparatorWordBudget_le le_rfl le_rfl le_rfl le_rfl hab I C

private theorem weightedSeparatorLoop_old_value (paid : Arcs V) (d : WeightedNetworkDemand V)
    (weight charges : V × V → ℕ) (scale fuel : ℕ) :
    (weightedCoverLoopWithSearchWork (weightedNetworkViolationWithSearchWork paid d weight scale) fuel charges).1 =
      weightedCoverLoop (weightedNetworkViolation paid d weight scale) fuel charges := by
  let search := weightedNetworkViolationWithSearchWork paid d weight scale
  let B := weightedSeparatorWorkBound (Fintype.card V) paid.card scale
  have each (state : V × V → ℕ) : (search state).2 ≤ B :=
    (weightedNetworkViolationWithSearchWork_spec paid d weight scale state).2
  have exactValue : (fun state => (search state).1) = weightedNetworkViolation paid d weight scale :=
    funext fun state => (weightedNetworkViolationWithSearchWork_spec paid d weight scale state).1
  obtain ⟨out, _⟩ := weightedCoverLoopWithSearchWork_spec search fuel B charges each
  rwa [exactValue] at out

private def weightedNetworkHistoryLoopWithWordWork (keys : List (V × V)) (distinct : keys.Nodup)
    (paid : Arcs V) (weight initial : V × V → ℕ × ℕ) (scale fuel : ℕ) :
    List (WeightedNetworkDemand V) → List (Arcs V) → List (Arcs V) × ℕ
  | [], history => (history, 3)
  | d :: D, history =>
    let separate := weightedNetworkViolationFromHistoryWithWordWork keys distinct paid d weight initial scale
    let first := weightedCoverLoopFromHistoryWithWordWork separate fuel history
    let last := weightedNetworkHistoryLoopWithWordWork keys distinct paid weight initial scale fuel D first.1.1
    (last.1, first.2 + last.2 + 10)

private theorem weightedNetworkHistoryLoopWithWordWork_spec (keys : List (V × V)) (distinct : keys.Nodup)
    (complete : ∀ e, e ∈ keys) (paid : Arcs V) (weight initial : V × V → ℕ × ℕ)
    (scale fuel W I C H : ℕ) (D : List (WeightedNetworkDemand V)) (history : List (Arcs V))
    (room : history.length + D.length * fuel ≤ H)
    (weightWork : ∀ e, (weight e).2 ≤ W) (initialLoad : ∀ e, (initial e).1 ≤ I)
    (initialWork : ∀ e, (initial e).2 ≤ C) :
    let start := fun e => (initial e).1
    let out := weightedNetworkHistoryLoopWithWordWork keys distinct paid weight initial scale fuel D history
    let old := weightedNetworkRunAtScaleWithSearchWork paid (fun e => (weight e).1) scale fuel D
      (history.foldr chargeWeightedCut start)
    let B := weightedHistorySeparatorWordBudget (Fintype.card V) paid.card scale W I C H
    out.1.foldr chargeWeightedCut start = old.1.1 ∧
      out.1 = old.1.2.reverse ++ history ∧ out.1.length ≤ H ∧
      out.2 ≤ D.length * (fuel * (B + 10) + 13) + 3 := by
  let start := fun e => (initial e).1
  let value := fun e => (weight e).1
  let B := weightedHistorySeparatorWordBudget (Fintype.card V) paid.card scale W I C H
  induction D generalizing history with
  | nil => simpa [weightedNetworkHistoryLoopWithWordWork, weightedNetworkRunAtScaleWithSearchWork] using room
  | cons d D ih =>
    let separate := weightedNetworkViolationFromHistoryWithWordWork keys distinct paid d weight initial scale
    let first := weightedCoverLoopFromHistoryWithWordWork separate fuel history
    let oldFirst := weightedCoverLoopWithSearchWork (weightedNetworkViolationWithSearchWork paid d value scale)
      fuel (history.foldr chargeWeightedCut start)
    let tail := weightedNetworkHistoryLoopWithWordWork keys distinct paid weight initial scale fuel D first.1.1
    let oldTail := weightedNetworkRunAtScaleWithSearchWork paid value scale fuel D oldFirst.1.1
    have each (past : List (Arcs V)) :=
      weightedNetworkViolationFromHistoryWithWordWork_spec keys distinct complete paid d weight initial scale W I C past
        weightWork initialLoad initialWork
    have fits : history.length + fuel + D.length * fuel ≤ H := by
      simp only [List.length_cons, Nat.succ_mul] at room
      omega
    obtain ⟨firstValue, firstHistory, firstLength, _, firstWork⟩ :=
      weightedCoverLoopFromHistoryWithWordWork_spec separate (weightedNetworkViolation paid d value scale)
        start (fun past => (each past).1) H B fuel history (by omega)
        (fun past shorter => (each past).2.trans
          (weightedHistorySeparatorWordBudget_mono _ _ _ _ _ _ shorter))
    have firstExact : (first.1.1.foldr chargeWeightedCut start, first.1.2) = oldFirst.1 :=
      firstValue.trans (weightedSeparatorLoop_old_value paid d value _ scale fuel).symm
    have firstCharge : first.1.1.foldr chargeWeightedCut start = oldFirst.1.1 := congrArg Prod.fst firstExact
    have firstCuts : first.1.2 = oldFirst.1.2 := congrArg Prod.snd firstExact
    have roomAfter : first.1.1.length + D.length * fuel ≤ H := by
      change first.1.1.length ≤ _ at firstLength
      omega
    obtain ⟨tailValue, tailHistory, tailLength, tailWork⟩ := ih first.1.1 roomAfter
    rw [firstCharge] at tailValue tailHistory
    have outputValue : tail.1.foldr chargeWeightedCut start = oldTail.1.1 := tailValue
    have outputHistory : tail.1 = oldTail.1.2.reverse ++ first.1.1 := tailHistory
    have stored : first.1.1 = oldFirst.1.2.reverse ++ history := by
      change first.1.1 = first.1.2.reverse ++ history at firstHistory
      rwa [firstCuts] at firstHistory
    refine ⟨outputValue, ?_, tailLength, ?_⟩
    · change tail.1 = (oldFirst.1.2 ++ oldTail.1.2).reverse ++ history
      rw [outputHistory, stored, List.reverse_append, List.append_assoc]
    · change first.2 + tail.2 + 10 ≤ (D.length + 1) * (fuel * (B + 10) + 13) + 3
      change first.2 ≤ fuel * (B + 10) + 3 at firstWork
      change tail.2 ≤ D.length * (fuel * (B + 10) + 13) + 3 at tailWork
      rw [Nat.add_mul, Nat.one_mul]
      omega

private def reverseWeightedCutsWithWordWork {E : Type*} : List E → List E → List E × ℕ
  | [], acc => (acc, 2)
  | key :: tail, acc =>
    let rest := reverseWeightedCutsWithWordWork tail (key :: acc)
    (rest.1, rest.2 + 6)

private theorem reverseWeightedCutsWithWordWork_spec {E : Type*} (xs acc : List E) :
    reverseWeightedCutsWithWordWork xs acc = (xs.reverse ++ acc, 6 * xs.length + 2) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons key tail ih =>
    simp only [reverseWeightedCutsWithWordWork, ih, List.reverse_cons, List.length_cons, Nat.mul_succ,
      List.append_assoc, List.singleton_append]

/-- Run the weighted separator on explicit pair keys, starting with no
accepted cuts. Return exact charge reads, accepted cuts in arrival order,
and the work of constructing the capacities and choosing the cuts. -/
def weightedNetworkRunWithHistoryWork (keys : List (V × V)) (distinct : keys.Nodup)
    (paid : Arcs V) (weight initial : V × V → ℕ × ℕ) (scale fuel : ℕ)
    (D : List (WeightedNetworkDemand V)) : (((V × V) → ℕ × ℕ) × List (Arcs V)) × ℕ :=
  let out := weightedNetworkHistoryLoopWithWordWork keys distinct paid weight initial scale fuel D []
  let chronological := reverseWeightedCutsWithWordWork out.1 []
  ((fun key => weightedChargeHistoryWithWordWork initial key out.1, chronological.1),
    out.2 + chronological.2 + 7)

theorem weightedNetworkRunWithHistoryWork_spec (keys : List (V × V)) (distinct : keys.Nodup)
    (complete : ∀ e, e ∈ keys) (paid : Arcs V) (weight initial : V × V → ℕ × ℕ)
    (scale fuel W I C : ℕ) (D : List (WeightedNetworkDemand V))
    (weightWork : ∀ e, (weight e).2 ≤ W) (initialLoad : ∀ e, (initial e).1 ≤ I)
    (initialWork : ∀ e, (initial e).2 ≤ C) :
    let out := weightedNetworkRunWithHistoryWork keys distinct paid weight initial scale fuel D
    let old := weightedNetworkRunAtScaleWithSearchWork paid (fun e => (weight e).1) scale fuel D (fun e => (initial e).1)
    let H := D.length * fuel
    let n := Fintype.card V
    let B := weightedHistorySeparatorWordBudget n paid.card scale W I C H
    ((fun e => (out.1.1 e).1), out.1.2) = old.1 ∧
      (∀ e, (out.1.1 e).2 ≤ C + 3 + H * (12 * n^2 + 14)) ∧
      out.2 ≤ D.length * (fuel * (B + 10) + 13) + 6 * H + 12 := by
  let run := weightedNetworkHistoryLoopWithWordWork keys distinct paid weight initial scale fuel D []
  let old := weightedNetworkRunAtScaleWithSearchWork paid (fun e => (weight e).1) scale fuel D (fun e => (initial e).1)
  let n := Fintype.card V
  let H := D.length * fuel
  let B := weightedHistorySeparatorWordBudget n paid.card scale W I C H
  obtain ⟨charges, chronology, length, work⟩ :=
    weightedNetworkHistoryLoopWithWordWork_spec keys distinct complete paid weight initial scale fuel W I C H D []
      (by simp [H]) weightWork initialLoad initialWork
  have exactCharges : run.1.foldr chargeWeightedCut (fun e => (initial e).1) = old.1.1 := charges
  have exactHistory : run.1 = old.1.2.reverse := by
    change run.1 = old.1.2.reverse ++ [] at chronology
    simpa only [List.append_nil] using chronology
  have pairBound (cut : Arcs V) : cut.card ≤ n^2 := by
    simpa only [Fintype.card_prod, pow_two, n] using card_le_univ cut
  have lookup (key : V × V) := weightedChargeHistoryWithWordWork_spec initial key run.1 (n^2)
    (fun cut _ => pairBound cut)
  have lengthCap : run.1.length ≤ H := length
  have reversal := reverseWeightedCutsWithWordWork_spec run.1 []
  refine ⟨Prod.ext ?_ ?_, ?_, ?_⟩
  · funext e
    exact (lookup e).1.trans (congrFun exactCharges e)
  · change (reverseWeightedCutsWithWordWork run.1 []).1 = old.1.2
    rw [reversal, exactHistory]
    simp
  · intro e
    exact (lookup e).2.2.trans (by
      gcongr
      exact initialWork e)
  · change run.2 + (reverseWeightedCutsWithWordWork run.1 []).2 + 7 ≤
      D.length * (fuel * (B + 10) + 13) + 6 * H + 12
    rw [reversal]
    change run.2 + (6 * run.1.length + 2) + 7 ≤ _
    change run.2 ≤ D.length * (fuel * (B + 10) + 13) + 3 at work
    omega

/-- Each accepted cut adds at most one to any requested charge. -/
theorem weightedNetworkRunWithHistoryWork_charge_le (keys : List (V × V)) (distinct : keys.Nodup)
    (complete : ∀ e, e ∈ keys) (paid : Arcs V) (weight initial : V × V → ℕ × ℕ)
    (scale fuel W I C : ℕ) (D : List (WeightedNetworkDemand V))
    (weightWork : ∀ e, (weight e).2 ≤ W) (initialLoad : ∀ e, (initial e).1 ≤ I)
    (initialWork : ∀ e, (initial e).2 ≤ C) (e : V × V) :
    let run := weightedNetworkRunWithHistoryWork keys distinct paid weight initial scale fuel D
    (run.1.1 e).1 ≤ I + D.length*fuel := by
  let history := (weightedNetworkHistoryLoopWithWordWork keys distinct paid weight initial scale fuel D []).1
  have shape (cut : Arcs V) : cut.card ≤ (Fintype.card V)^2 := by
    simpa only [Fintype.card_prod, pow_two] using card_le_univ cut
  have length : history.length ≤ D.length*fuel :=
    (weightedNetworkHistoryLoopWithWordWork_spec keys distinct complete paid weight initial scale fuel
      W I C (D.length*fuel) D [] (by simp) weightWork initialLoad initialWork).2.2.1
  exact (weightedChargeHistoryWithWordWork_spec initial e history ((Fintype.card V)^2)
    (fun cut _ => shape cut)).2.1.trans (Nat.add_le_add (initialLoad e) length)

private def unitFlowFromRoutes (paths : List (List (V × V))) : ArcFlow V :=
  paths.foldr (fun path flow => augmentArcFlow flow path.toFinset) (fun _ => 0)

private def readUnitFlowFromRoutesWithWordWork (key : V × V) : List (List (V × V)) → ℤ × ℕ
  | [] => (0,3)
  | path::earlier =>
    let forward := memScanWithWordWork key path
    let backward := memScanWithWordWork key.swap path
    let past := readUnitFlowFromRoutesWithWordWork key earlier
    (past.1+(if forward.1 then 1 else 0)-(if backward.1 then 1 else 0),
      past.2+forward.2+backward.2+10)

omit [Fintype V] in
private theorem readUnitFlowFromRoutesWithWordWork_spec (key : V × V) (paths : List (List (V × V)))
    (n : ℕ) (bounded : ∀ path ∈ paths, path.length ≤ n) :
    let out := readUnitFlowFromRoutesWithWordWork key paths
    out.1 = unitFlowFromRoutes paths key ∧ out.2 ≤ paths.length*(4*n+12)+3 := by
  induction paths with
  | nil => simp [readUnitFlowFromRoutesWithWordWork,unitFlowFromRoutes]
  | cons path earlier ih =>
    obtain ⟨same,work⟩ := ih (fun p on => bounded p (List.mem_cons_of_mem _ on))
    obtain ⟨forward,readForward⟩ := memScanWithWordWork_spec key path
    obtain ⟨backward,readBack⟩ := memScanWithWordWork_spec key.swap path
    have length := bounded path List.mem_cons_self
    refine ⟨?_,?_⟩
    · change (readUnitFlowFromRoutesWithWordWork key earlier).1+
          (if (memScanWithWordWork key path).1 then 1 else 0)-
          (if (memScanWithWordWork key.swap path).1 then 1 else 0) =
        unitFlowFromRoutes (path::earlier) key
      rw [same,forward,backward]
      change _ =
        unitFlowFromRoutes earlier key+(if key ∈ path.toFinset then 1 else 0)-
          (if key.swap ∈ path.toFinset then 1 else 0)
      simp
    · simp only [readUnitFlowFromRoutesWithWordWork,List.length_cons]
      rw [Nat.succ_mul earlier.length (4*n+12)]
      omega

private def residualCapacityRowsWithWordWork (paths : List (List (V × V))) :
    List ((V × V) × ℤ) → List (V × V) × ℕ
  | [] => ([],3)
  | row::rows =>
    let current := readUnitFlowFromRoutesWithWordWork row.1 paths
    let rest := residualCapacityRowsWithWordWork paths rows
    let kept := if current.1 < row.2 then row.1::rest.1 else rest.1
    (kept,current.2+rest.2+10)

omit [Fintype V] in
private theorem residualCapacityRowsWithWordWork_spec (paths : List (List (V × V)))
    (rows : List ((V × V) × ℤ)) (n : ℕ) (bounded : ∀ path ∈ paths, path.length ≤ n) :
    let out := residualCapacityRowsWithWordWork paths rows
    (∀ e, e ∈ out.1 ↔ ∃ row ∈ rows, row.1 = e ∧ unitFlowFromRoutes paths e < row.2) ∧
      out.1.length ≤ rows.length ∧ out.2 ≤ rows.length*(paths.length*(4*n+12)+13)+3 := by
  induction rows with
  | nil => simp [residualCapacityRowsWithWordWork]
  | cons row rows ih =>
    obtain ⟨same,work⟩ := readUnitFlowFromRoutesWithWordWork_spec row.1 paths n bounded
    obtain ⟨existing,size,spent⟩ := ih
    have fee : (residualCapacityRowsWithWordWork paths (row::rows)).2 ≤
        (row::rows).length*(paths.length*(4*n+12)+13)+3 := by
      simp only [residualCapacityRowsWithWordWork,List.length_cons]
      rw [Nat.succ_mul rows.length (paths.length*(4*n+12)+13)]
      omega
    refine ⟨?_,?_,fee⟩
    · intro e
      simp only [residualCapacityRowsWithWordWork,same]
      by_cases pass : unitFlowFromRoutes paths row.1 < row.2
      · simp only [pass,ite_true,List.mem_cons,existing]
        constructor
        · rintro (rfl | ⟨r,member,eq,flow⟩)
          · exact ⟨row,Or.inl rfl,rfl,pass⟩
          · exact ⟨r,Or.inr member,eq,flow⟩
        · rintro ⟨r,(rfl | member),eq,flow⟩
          · exact Or.inl eq.symm
          · exact Or.inr ⟨r,member,eq,flow⟩
      · simp only [pass,ite_false,existing,List.mem_cons]
        constructor
        · rintro ⟨r,member,eq,flow⟩
          exact ⟨r,Or.inr member,eq,flow⟩
        · rintro ⟨r,(rfl | member),eq,flow⟩
          · exact (pass (eq.symm ▸ flow)).elim
          · exact ⟨r,member,eq,flow⟩
    · simp only [residualCapacityRowsWithWordWork,same,List.length_cons]
      split
      · simpa only [List.length_cons] using Nat.succ_le_succ size
      · exact size.trans (Nat.le_succ _)

private theorem residualCapacityRowsWithWordWork_set (paths : List (List (V × V)))
    (keys : List (V × V)) (complete : ∀ e, e ∈ keys) (capacity : ArcFlow V)
    (n : ℕ) (bounded : ∀ path ∈ paths, path.length ≤ n) :
    (residualCapacityRowsWithWordWork paths (keys.map (fun e => (e,capacity e)))).1.toFinset =
      residualArcs capacity (unitFlowFromRoutes paths) := by
  ext e
  rw [List.mem_toFinset,(residualCapacityRowsWithWordWork_spec paths _ n bounded).1 e]
  simp only [residualArcs,mem_filter,mem_univ,true_and,List.mem_map]
  constructor
  · rintro ⟨row,⟨x,_,rfl⟩,rfl,flow⟩
    exact flow
  · intro flow
    exact ⟨(e,capacity e),⟨e,complete e,rfl⟩,rfl,flow⟩

private def augmentFromCapacityRowsWithWordWork (rows : List ((V × V) × ℤ)) (s t : V)
    (depth : ℕ) : ℕ → List (List (V × V)) → (List (List (V × V)) × ℕ) × ℕ
  | 0, paths => ((paths,0),3)
  | fuel+1, paths =>
    let graph := residualCapacityRowsWithWordWork paths rows
    let route := routePathListWithWordWork graph.1 s t depth
    match route.1 with
    | none => ((paths,0),graph.2+route.2+7)
    | some edges =>
      let later := augmentFromCapacityRowsWithWordWork rows s t depth fuel (edges::paths)
      ((later.1.1,later.1.2+1),graph.2+route.2+later.2+12)

private def residualPathRowsWordBudget (n supply : ℕ) : ℕ :=
  n^2*(supply*(4*n+12)+13)+3

private def weightedResidualRowsStepWordBudget (n supply : ℕ) : ℕ :=
  residualPathRowsWordBudget n supply + routePathListWordBudget n (n^2) + 12

private theorem routePath_length_le_vertices (G : Arcs V) (s t : V) (edges : List (V × V))
    (chosen : routePath G s t = some edges) : edges.length ≤ Fintype.card V := by
  have simple := (routePath_some chosen).2
  have large := Finset.card_le_univ (edges.map Prod.fst ++ [t]).toFinset
  rw [List.toFinset_card_of_nodup simple,List.length_append,List.length_map,List.length_singleton] at large
  exact (Nat.le_succ _).trans large

private theorem augmentFromCapacityRowsWithWordWork_spec
    (keys : List (V × V)) (complete : ∀ e, e ∈ keys)
    (size : keys.length ≤ (Fintype.card V)^2) (cap : ArcFlow V) (s t : V) (supply fuel : ℕ)
    (paths : List (List (V × V))) (room : paths.length+fuel ≤ supply)
    (bounded : ∀ path ∈ paths, path.length ≤ Fintype.card V) :
    let n := Fintype.card V
    let out := augmentFromCapacityRowsWithWordWork (keys.map fun e => (e,cap e)) s t n fuel paths
    (unitFlowFromRoutes out.1.1,out.1.2) = unitAugmentations cap s t fuel (unitFlowFromRoutes paths) ∧
      out.1.1.length ≤ paths.length+fuel ∧
      (∀ path ∈ out.1.1, path.length ≤ n) ∧ out.2 ≤ fuel*weightedResidualRowsStepWordBudget n supply+3 := by
  let n := Fintype.card V
  let rows := keys.map (fun e => (e,cap e))
  let Budget := weightedResidualRowsStepWordBudget n supply
  induction fuel generalizing paths with
  | zero => simpa [augmentFromCapacityRowsWithWordWork,unitAugmentations] using bounded
  | succ fuel ih =>
    let graph := residualCapacityRowsWithWordWork paths rows
    let route := routePathListWithWordWork graph.1 s t n
    have graphExact : graph.1.toFinset = residualArcs cap (unitFlowFromRoutes paths) :=
      residualCapacityRowsWithWordWork_set paths keys complete cap n bounded
    obtain ⟨_,length,graphWork⟩ := residualCapacityRowsWithWordWork_spec paths rows n bounded
    change graph.1.length ≤ rows.length at length
    change graph.2 ≤ rows.length*(paths.length*(4*n+12)+13)+3 at graphWork
    have rowSize : rows.length ≤ n^2 := (List.length_map _).trans_le size
    have inside : paths.length ≤ supply := by omega
    have work : graph.2 ≤ residualPathRowsWordBudget n supply :=
      graphWork.trans (Nat.add_le_add_right (Nat.mul_le_mul rowSize
        (Nat.add_le_add_right (Nat.mul_le_mul_right _ inside) 13)) 3)
    obtain ⟨same,spent⟩ := routePathListWithWordWork_spec graph.1 s t
    change route.1 = routePath graph.1.toFinset s t at same
    rw [graphExact] at same
    have routing : route.2 ≤ routePathListWordBudget n (n^2) :=
      spent.trans (routePathListWordBudget_mono_arcs n (length.trans rowSize))
    change let out := augmentFromCapacityRowsWithWordWork rows s t n (fuel+1) paths
      (unitFlowFromRoutes out.1.1,out.1.2) = unitAugmentations cap s t (fuel+1) (unitFlowFromRoutes paths) ∧
        out.1.1.length ≤ paths.length+(fuel+1) ∧ (∀ p ∈ out.1.1, p.length ≤ n) ∧ out.2 ≤ (fuel+1)*Budget+3
    cases chosen : route.1 with
    | none =>
      have reference := same.symm.trans chosen
      have unfoldStep : augmentFromCapacityRowsWithWordWork rows s t n (fuel+1) paths =
          ((paths,0),graph.2+route.2+7) := by
        rw [augmentFromCapacityRowsWithWordWork]
        change (match route.1 with
          | none => ((paths,0),graph.2+route.2+7)
          | some edges =>
            let later := augmentFromCapacityRowsWithWordWork rows s t n fuel (edges::paths)
            ((later.1.1,later.1.2+1),graph.2+route.2+later.2+12)) = _
        rw [chosen]
      simp only [unfoldStep,unitAugmentations,reference,true_and]
      refine ⟨Nat.le_add_right _ _,bounded,?_⟩
      rw [Nat.succ_mul fuel Budget]
      have step : graph.2+route.2+12 ≤ Budget := Nat.add_le_add_right (Nat.add_le_add work routing) 12
      omega
    | some path =>
      have reference := same.symm.trans chosen
      have routeSize := routePath_length_le_vertices _ _ _ _ reference
      have allowed : ∀ p ∈ path::paths, p.length ≤ n := by
        intro p on
        rcases List.mem_cons.mp on with rfl | old
        · exact routeSize
        · exact bounded p old
      have more : (path::paths).length+fuel ≤ supply := by simp only [List.length_cons]; omega
      let later := augmentFromCapacityRowsWithWordWork rows s t n fuel (path::paths)
      obtain ⟨sameRest,restLength,restOk,restWork⟩ := ih (path::paths) more allowed
      have next : unitFlowFromRoutes (path::paths) = augmentArcFlow (unitFlowFromRoutes paths) path.toFinset := rfl
      rw [next] at sameRest
      have unfoldStep : augmentFromCapacityRowsWithWordWork rows s t n (fuel+1) paths =
          ((later.1.1,later.1.2+1),graph.2+route.2+later.2+12) := by
        rw [augmentFromCapacityRowsWithWordWork]
        change (match route.1 with
          | none => ((paths,0),graph.2+route.2+7)
          | some edges =>
            let later := augmentFromCapacityRowsWithWordWork rows s t n fuel (edges::paths)
            ((later.1.1,later.1.2+1),graph.2+route.2+later.2+12)) = _
        rw [chosen]
      simp only [unfoldStep,unitAugmentations,reference]
      refine ⟨?_,?_,restOk,?_⟩
      · have augRest : (unitFlowFromRoutes later.1.1,later.1.2) =
            unitAugmentations cap s t fuel (augmentArcFlow (unitFlowFromRoutes paths) path.toFinset) := sameRest
        exact congrArg (fun r : ArcFlow V × ℕ => (r.1,r.2+1)) augRest
      · exact restLength.trans_eq (by simp only [List.length_cons]; omega)
      · change later.2 ≤ fuel*Budget+3 at restWork
        rw [Nat.succ_mul fuel Budget]
        have step : graph.2+route.2+12 ≤ Budget := Nat.add_le_add_right (Nat.add_le_add work routing) 12
        omega

/-- Search residual capacity rows using a supplied vertex count and an
explicit history of augmenting paths. -/
def findLowCapacityCutFromHistoryRowsWithWordWork (rows : CapacityRows V) (s t : V)
    (depth supply : ℕ) : Option (Finset V) × ℕ :=
  let run := augmentFromCapacityRowsWithWordWork rows.val s t depth supply []
  if run.1.2 = supply then (none,run.2+6)
  else
    let residual := residualCapacityRowsWithWordWork run.1.1 rows.val
    let side := sourceSideFromResidualListWithWordWork residual.1 s depth
    (some side.1,run.2+residual.2+side.2+10)

def weightedResidualRowsSearchWordBudget (n supply : ℕ) : ℕ :=
  supply*weightedResidualRowsStepWordBudget n supply+residualPathRowsWordBudget n supply+
    reachInListWordBudget n (n^2)+7*n^2+19

theorem findLowCapacityCutFromHistoryRowsWithWordWork_spec (rows : CapacityRows V)
    (keys : List (V × V)) (unique : keys.Nodup) (complete : ∀ e, e ∈ keys)
    (capacity : ArcFlow V) (exactRows : rows.val = keys.map (fun e => (e,capacity e)))
    (s t : V) (depth supply : ℕ) (size : depth = Fintype.card V) :
    let out := findLowCapacityCutFromHistoryRowsWithWordWork rows s t depth supply
    out.1 = findLowCapacityCut capacity s t supply ∧
      out.2 ≤ weightedResidualRowsSearchWordBudget depth supply := by
  subst depth
  let n := Fintype.card V
  let run := augmentFromCapacityRowsWithWordWork rows.val s t n supply []
  have count : keys.length ≤ n^2 := by
    rw [← List.toFinset_card_of_nodup unique]
    simpa only [n,pow_two,Fintype.card_prod] using Finset.card_le_univ keys.toFinset
  obtain ⟨aug,length,paths,work⟩ := augmentFromCapacityRowsWithWordWork_spec keys complete count capacity s t supply supply []
    (by simp) (by simp)
  rw [← exactRows] at aug length paths work
  have equal : (unitFlowFromRoutes run.1.1,run.1.2) = unitAugmentations capacity s t supply (fun _ => 0) := aug
  have small : run.1.1.length ≤ supply := by simpa only [List.length_nil,Nat.zero_add] using length
  have cost : run.2 ≤ supply*weightedResidualRowsStepWordBudget n supply+3 := work
  let res := residualCapacityRowsWithWordWork run.1.1 rows.val
  have resExact : res.1.toFinset = residualArcs capacity (unitFlowFromRoutes run.1.1) := by
    rw [show res = residualCapacityRowsWithWordWork run.1.1 rows.val from rfl,exactRows]
    exact residualCapacityRowsWithWordWork_set run.1.1 keys complete capacity n paths
  obtain ⟨_,len,scan⟩ := residualCapacityRowsWithWordWork_spec run.1.1 rows.val n paths
  have rowSize : rows.val.length ≤ n^2 := by rw [exactRows,List.length_map]; exact count
  have resLen : res.1.length ≤ n^2 := len.trans rowSize
  have resWork : res.2 ≤ residualPathRowsWordBudget n supply := scan.trans
    (Nat.add_le_add_right (Nat.mul_le_mul rowSize (Nat.add_le_add_right (Nat.mul_le_mul_right _ small) 13)) 3)
  let side := sourceSideFromResidualListWithWordWork res.1 s n
  obtain ⟨same,sideWork⟩ := sourceSideFromResidualListWithWordWork_spec res.1 s
  have sideEq : side.1 = residualReach capacity (unitFlowFromRoutes run.1.1) s := by
    change side.1 = reaches (reverseArcs (residualArcs capacity (unitFlowFromRoutes run.1.1))) s
    exact same.trans (by rw [resExact])
  have sideCost : side.2 ≤ reachInListWordBudget n (n^2)+7*n^2+6 := by
    apply sideWork.trans
    unfold reachInListWordBudget
    gcongr
  have countEq := congrArg Prod.snd equal
  have flowEq := congrArg Prod.fst equal
  change run.1.2 = (unitAugmentations capacity s t supply (fun _ => 0)).2 at countEq
  change unitFlowFromRoutes run.1.1 = (unitAugmentations capacity s t supply (fun _ => 0)).1 at flowEq
  unfold findLowCapacityCutFromHistoryRowsWithWordWork findLowCapacityCut
  dsimp only
  rw [← show run = augmentFromCapacityRowsWithWordWork rows.val s t n supply [] from rfl, ← countEq]
  by_cases full : run.1.2 = supply
  · simp only [full,ite_true,true_and]
    change run.2+6 ≤ weightedResidualRowsSearchWordBudget n supply
    exact (Nat.add_le_add_right cost 6).trans (by unfold weightedResidualRowsSearchWordBudget; omega)
  · simp only [full,ite_false,Option.some.injEq]
    refine ⟨sideEq.trans (congrArg (fun f => residualReach capacity f s) flowEq),?_⟩
    change run.2+res.2+side.2+10 ≤ weightedResidualRowsSearchWordBudget n supply
    calc
      _ ≤ (supply*weightedResidualRowsStepWordBudget n supply+3)+residualPathRowsWordBudget n supply+
          (reachInListWordBudget n (n^2)+7*n^2+6)+10 :=
        Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add cost resWork) sideCost) 10
      _ = _ := by unfold weightedResidualRowsSearchWordBudget; omega


end Capacity

end OnlineReachabilityPreservers
