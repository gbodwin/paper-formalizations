import OnlineReachabilityPreservers.SteinerBinaryWeightedCapacityWork
import OnlineReachabilityPreservers.SteinerBinaryFlowRunWork
import OnlineReachabilityPreservers.SteinerClippedFlowCut
import OnlineReachabilityPreservers.SteinerWeightedNetwork

/-! Run the weighted separator on the stored binary paid-edge states. -/

namespace OnlineReachabilityPreservers

/-- The binary labels of an ordered pair and its state if the pair is paid. -/
structure BinaryWeightedPairRow (V : Type*) where
  arc : V × V
  labels : List Bool × List Bool
  paid : Option (List Bool × BinaryWeightedLoad)

variable {V : Type*} [LinearOrder V] [Fintype V]

/-- Each paid entry carries the fixed cost and the current weighted load. -/
def BinaryWeightedPairRow.Encodes (row : BinaryWeightedPairRow V) (edges : Arcs V)
    (weight charges : V × V → ℕ) (code : V → List Bool) (costWidth amountWidth : ℕ) : Prop :=
  row.labels = (code row.arc.1,code row.arc.2) ∧
  (row.arc ∈ edges → ∃ cost state, row.paid = some (cost,state) ∧
    binaryWordValue cost = weight row.arc ∧ state.Encodes (weight row.arc) (charges row.arc) ∧
    cost.length ≤ costWidth ∧ state.amount.length ≤ amountWidth) ∧
  (row.arc ∉ edges → row.paid = none)

/-- Free attachments take precedence over paid capacities. Missing pairs
have zero capacity. The paid capacities are clipped at the query supply. -/
def binaryWeightedCapacityAtWithWork (free : List (List Bool × List Bool)) (ceiling : List Bool)
    (supply : ℕ) (row : BinaryWeightedPairRow V) : List Bool × ℕ :=
  let allowed := binaryArcMemWithWork row.labels free
  if allowed.1 then (ceiling,allowed.2+5) else
    match row.paid with
    | none => ([],allowed.2+5)
    | some (cost,state) =>
      let capacity := binaryClippedWeightedCapacityWithWork cost state supply
      (capacity.1,allowed.2+capacity.2+5)

def binaryWeightedCapacityAtWorkBudget (free labels cost amount supply : ℕ) : ℕ :=
  2+free*(10*labels+14)+binaryCeilingDivWorkBudget amount cost 0 0 supply+5

omit [Fintype V] in
theorem binaryWeightedCapacityAtWithWork_spec (edges : Arcs V) (weight charges : V × V → ℕ)
    (positive : ∀ e ∈ edges, 0 < weight e) (free : List (V × V)) (source target : V) (supply : ℕ)
    (ceiling : List Bool) (supplyWord : binaryWordValue ceiling = supply) (code : V → List Bool)
    (injective : Function.Injective code) (labels costWidth amountWidth : ℕ) (bounded : ∀ v, (code v).length ≤ labels)
    (row : BinaryWeightedPairRow V) (encoded : row.Encodes edges weight charges code costWidth amountWidth) :
    let demand : WeightedNetworkDemand V := ⟨free.toFinset,source,target⟩
    let out := binaryWeightedCapacityAtWithWork (binaryEncodeArcs code free) ceiling supply row
    (binaryWordValue out.1 : ℤ) = min (weightedNetworkCapacity edges demand weight charges supply row.arc) (supply : ℤ) ∧
    out.1.length ≤ max ceiling.length supply ∧
    out.2 ≤ binaryWeightedCapacityAtWorkBudget free.length labels costWidth amountWidth supply := by
  let allowed := binaryArcMemWithWork row.labels (binaryEncodeArcs code free)
  rcases encoded with ⟨sameLabels,paid,unpaid⟩
  obtain ⟨test,cost⟩ := binaryArcMemWithWork_spec code injective labels bounded row.arc free
  rw [← sameLabels] at test cost
  change allowed.1 = decide (row.arc ∈ free) at test
  change allowed.2 ≤ 2+free.length*(10*labels+14) at cost
  dsimp only [binaryWeightedCapacityAtWithWork]
  by_cases attach : row.arc ∈ free
  · rw [test,decide_eq_true attach,ite_eq_left (show true = true from rfl)]
    refine ⟨?_,le_max_left _ _,?_⟩
    · simp [weightedNetworkCapacity,attach,supplyWord]
    · change allowed.2+5 ≤ _
      unfold binaryWeightedCapacityAtWorkBudget
      omega
  · rw [test,decide_eq_false attach,ite_eq_right (show ¬ false = true from by decide)]
    by_cases isPaid : row.arc ∈ edges
    · obtain ⟨costWord,state,readCost,decodeCost,represented,shortCost,shortAmount⟩ := paid isPaid
      rw [readCost]
      have costPositive : 0 < binaryWordValue costWord := by rw [decodeCost]; exact positive row.arc isPaid
      have stateExact : state.Encodes (binaryWordValue costWord) (charges row.arc) := by rwa [decodeCost]
      obtain ⟨value,width,work⟩ := binaryClippedWeightedCapacityWithWork_spec costWord state (charges row.arc) supply
        costPositive stateExact
      have fits := work.trans (binaryCeilingDivWorkBudget_mono_widths shortAmount shortCost 0 0 supply)
      refine ⟨?_,width.trans (le_max_right _ _),?_⟩
      · change (binaryWordValue (binaryClippedWeightedCapacityWithWork costWord state supply).1 : ℤ) = _
        rw [value,decodeCost]
        simp [weightedNetworkCapacity,attach,isPaid,Nat.cast_min,min_comm]
      · unfold binaryWeightedCapacityAtWorkBudget
        change allowed.2+(binaryClippedWeightedCapacityWithWork costWord state supply).2+5 ≤ _
        omega
    · rw [unpaid isPaid]
      refine ⟨?_,Nat.zero_le _,?_⟩
      · simp [weightedNetworkCapacity,attach,isPaid,binaryWordValue]
      · change allowed.2+5 ≤ _
        unfold binaryWeightedCapacityAtWorkBudget
        omega

/-- Build the capacity words in the supplied complete key order. -/
def binaryWeightedCapacityRowsWithWork (free : List (List Bool × List Bool)) (ceiling : List Bool) (supply : ℕ) :
    List (BinaryWeightedPairRow V) → List ((List Bool × List Bool) × List Bool) × ℕ
  | [] => ([],2)
  | row::rest =>
    let head := binaryWeightedCapacityAtWithWork free ceiling supply row
    let tail := binaryWeightedCapacityRowsWithWork free ceiling supply rest
    ((row.labels,head.1)::tail.1,head.2+tail.2+4)

def binaryWeightedCapacityRowsWorkBudget (rows free labels cost amount supply : ℕ) : ℕ :=
  2+rows*(binaryWeightedCapacityAtWorkBudget free labels cost amount supply+4)

omit [Fintype V] in
theorem binaryWeightedCapacityRowsWithWork_spec (edges : Arcs V) (weight charges : V × V → ℕ)
    (positive : ∀ e ∈ edges, 0 < weight e) (free : List (V × V)) (source target : V) (supply : ℕ)
    (ceiling : List Bool) (supplyWord : binaryWordValue ceiling = supply) (code : V → List Bool)
    (injective : Function.Injective code) (labels costWidth amountWidth : ℕ) (bounded : ∀ v, (code v).length ≤ labels)
    (rows : List (BinaryWeightedPairRow V)) (represented : ∀ row ∈ rows, row.Encodes edges weight charges code costWidth amountWidth) :
    let demand : WeightedNetworkDemand V := ⟨free.toFinset,source,target⟩
    let capacity : ArcFlow V := fun e => min (weightedNetworkCapacity edges demand weight charges supply e) (supply : ℤ)
    let out := binaryWeightedCapacityRowsWithWork (binaryEncodeArcs code free) ceiling supply rows
    (∃ actual : List ((V × V) × List Bool), out.1 = binaryEncodeCapacityRows code actual ∧
      actual.map Prod.fst = rows.map BinaryWeightedPairRow.arc ∧
      (∀ row ∈ actual, (binaryWordValue row.2 : ℤ) = capacity row.1 ∧ row.2.length ≤ max ceiling.length supply)) ∧
    out.2 ≤ binaryWeightedCapacityRowsWorkBudget rows.length free.length labels costWidth amountWidth supply := by
  induction rows with
  | nil =>
    refine ⟨⟨[],rfl,rfl,by simp⟩,?_⟩
    simp [binaryWeightedCapacityRowsWithWork,binaryWeightedCapacityRowsWorkBudget]
  | cons row rest ih =>
    let head := binaryWeightedCapacityAtWithWork (binaryEncodeArcs code free) ceiling supply row
    let tail := binaryWeightedCapacityRowsWithWork (binaryEncodeArcs code free) ceiling supply rest
    let fee := binaryWeightedCapacityAtWorkBudget free.length labels costWidth amountWidth supply
    have current := represented row List.mem_cons_self
    obtain ⟨value,width,headCost⟩ := binaryWeightedCapacityAtWithWork_spec edges weight charges positive free source target supply
      ceiling supplyWord code injective labels costWidth amountWidth bounded row current
    obtain ⟨⟨packed,encoded,keys,correct⟩,tailCost⟩ := ih (fun entry present => represented entry (List.mem_cons_of_mem _ present))
    change tail.1 = _ at encoded
    change head.2 ≤ fee at headCost
    change tail.2 ≤ 2+rest.length*(fee+4) at tailCost
    refine ⟨⟨(row.arc,head.1)::packed,?_,?_,?_⟩,?_⟩
    · change (row.labels,head.1)::tail.1 = _
      rw [current.1,encoded]
      rfl
    · simpa only [List.map_cons] using congrArg (row.arc::·) keys
    · intro entry member
      rcases List.mem_cons.mp member with rfl | present
      · exact ⟨value,width⟩
      · exact correct entry present
    · change head.2+tail.2+4 ≤ 2+(rest.length+1)*(fee+4)
      rw [Nat.add_mul,Nat.one_mul]
      omega

/-- Assemble request-local capacities from the represented states and run
the bounded binary separator on the original paid arcs. -/
def binaryWeightedViolationWithWork (arcs free : List (List Bool × List Bool)) (ceiling : List Bool)
    (rows : List (BinaryWeightedPairRow V)) (source target : List Bool) (depth supply : ℕ) :
    Option (List (List Bool × List Bool)) × ℕ :=
  let capacity := binaryWeightedCapacityRowsWithWork free ceiling supply rows
  let cut := binaryFindLowCapacityOutgoingCutWithWork arcs capacity.1 source target depth supply
  (cut.1,capacity.2+cut.2+5)

/-- The paid cut is exactly the reference weighted violation. Free arcs
are installed with full supply and take precedence over overlapping paid
states. The pair states and the request's free rows are supplied. -/
theorem binaryWeightedViolationWithWork_refines (arcs free : List (V × V)) (source target : V) (supply : ℕ)
    (weight charges : V × V → ℕ) (positive : ∀ e ∈ arcs.toFinset, 0 < weight e)
    (ceiling : List Bool) (supplyWord : binaryWordValue ceiling = supply) (code : V → List Bool)
    (injective : Function.Injective code) (labels costWidth amountWidth : ℕ) (bounded : ∀ v, (code v).length ≤ labels)
    (rows : List (BinaryWeightedPairRow V)) (complete : ∀ e, e ∈ rows.map BinaryWeightedPairRow.arc)
    (represented : ∀ row ∈ rows, row.Encodes arcs.toFinset weight charges code costWidth amountWidth) :
    let demand : WeightedNetworkDemand V := ⟨free.toFinset,source,target⟩
    let out := binaryWeightedViolationWithWork (binaryEncodeArcs code arcs) (binaryEncodeArcs code free)
      ceiling rows (code source) (code target) (Fintype.card V) supply
    (match weightedNetworkViolation arcs.toFinset demand weight supply charges with
      | none => out.1 = none
      | some C => ∃ cut : List (V × V), out.1 = some (binaryEncodeArcs code cut) ∧
        cut.toFinset = C ∧ (arcs.Nodup → cut.Nodup)) ∧
    out.2 ≤ binaryWeightedCapacityRowsWorkBudget rows.length free.length labels costWidth amountWidth supply+
      binaryLowCapacityOutgoingCutWorkBudget (Fintype.card V) arcs.length rows.length labels (max ceiling.length supply) supply+5 := by
  let demand : WeightedNetworkDemand V := ⟨free.toFinset,source,target⟩
  let reference := weightedNetworkCapacity arcs.toFinset demand weight charges supply
  let capacity := binaryWeightedCapacityRowsWithWork (binaryEncodeArcs code free) ceiling supply rows
  let cut := binaryFindLowCapacityOutgoingCutWithWork (binaryEncodeArcs code arcs) capacity.1 (code source) (code target)
    (Fintype.card V) supply
  obtain ⟨⟨packed,encoded,keys,correct⟩,capacityCost⟩ := binaryWeightedCapacityRowsWithWork_spec arcs.toFinset weight charges
    positive free source target supply ceiling supplyWord code injective labels costWidth amountWidth bounded rows represented
  change capacity.1 = binaryEncodeCapacityRows code packed at encoded
  have indexed : ∀ e, e ∈ packed.map Prod.fst := by intro e; rw [keys]; exact complete e
  have count : packed.length = rows.length := by
    have lengths := congrArg List.length keys
    simpa only [List.length_map] using lengths
  obtain ⟨result,work⟩ := binaryFindLowCapacityOutgoingCutWithWork_refines
    (capacity := fun e => min (reference e) (supply : ℤ)) code injective labels bounded arcs packed source target
    (max ceiling.length supply) supply indexed correct
  rw [← encoded,count] at work
  rw [← encoded] at result
  have same := findLowCapacityCut_clip_to_supply reference source target supply
    (weightedNetworkCapacity_nonneg arcs.toFinset demand weight charges supply)
  change (match findLowCapacityCut (fun e => min (reference e) (supply : ℤ)) source target supply with
    | none => cut.1 = none
    | some side => ∃ C : List (V × V), cut.1 = some (binaryEncodeArcs code C) ∧
      C.toFinset = outgoingCut arcs.toFinset side ∧ (arcs.Nodup → C.Nodup)) at result
  rw [same] at result
  refine ⟨?_,?_⟩
  · change (match (findLowCapacityCut reference source target supply).map (outgoingCut arcs.toFinset) with
      | none => cut.1 = none
      | some C => ∃ selected : List (V × V), cut.1 = some (binaryEncodeArcs code selected) ∧
        selected.toFinset = C ∧ (arcs.Nodup → selected.Nodup))
    cases found : findLowCapacityCut reference source target supply <;>
      simpa only [found,Option.map_none,Option.map_some] using result
  · change capacity.2+cut.2+5 ≤ _
    exact Nat.add_le_add_right (Nat.add_le_add capacityCost work) 5

end OnlineReachabilityPreservers
