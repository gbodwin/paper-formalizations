import OnlineReachabilityPreservers.SteinerBinaryWeightedCutWork
import OnlineReachabilityPreservers.SteinerBinaryFinOutputWork
import OnlineReachabilityPreservers.SteinerDyadicRounding

/-! Read the capacity used by forest rounding directly from the binary paid table. -/

namespace OnlineReachabilityPreservers

private def findBinaryWeightedPairWithWork {V : Type*} (query : List Bool × List Bool) :
    List (BinaryWeightedPairRow V) → Option (BinaryWeightedPairRow V) × ℕ
  | [] => (none,2)
  | row :: rest =>
    let found := binaryArcMemWithWork query [row.labels]
    if found.1 then (some row,found.2+5) else
      let tail := findBinaryWeightedPairWithWork query rest
      (tail.1,found.2+tail.2+6)

private theorem findBinaryWeightedPairWithWork_spec {V : Type*} [DecidableEq V]
    (code : V → List Bool) (injective : Function.Injective code) (labels : ℕ)
    (bounded : ∀ v, (code v).length ≤ labels) (key : V × V) (rows : List (BinaryWeightedPairRow V))
    (encoded : ∀ row ∈ rows, row.labels = (code row.arc.1,code row.arc.2)) :
    let out := findBinaryWeightedPairWithWork (code key.1,code key.2) rows
    (match out.1 with
      | none => key ∉ rows.map BinaryWeightedPairRow.arc
      | some row => row ∈ rows ∧ row.arc = key) ∧ out.2 ≤ 2+rows.length*(10*labels+22) := by
  induction rows with
  | nil => simp [findBinaryWeightedPairWithWork]
  | cons row rest ih =>
    let query := (code key.1,code key.2)
    let lower := findBinaryWeightedPairWithWork query rest
    let found := binaryArcMemWithWork query [row.labels]
    have same := encoded row List.mem_cons_self
    obtain ⟨tail,tailWork⟩ := ih (fun r inTail => encoded r (List.mem_cons_of_mem _ inTail))
    have shape : binaryEncodeArcs code [row.arc] = [row.labels] := by simp [binaryEncodeArcs,same]
    obtain ⟨value,searchWork⟩ := binaryArcMemWithWork_spec code injective labels bounded key [row.arc]
    rw [shape] at value searchWork
    change found.1 = decide (key ∈ [row.arc]) at value
    change found.2 ≤ 2+1*(10*labels+14) at searchWork
    change lower.2 ≤ 2+rest.length*(10*labels+22) at tailWork
    dsimp only [findBinaryWeightedPairWithWork]
    change (match (if found.1 then _ else _ : Option (BinaryWeightedPairRow V) × ℕ).1 with
      | none => key ∉ (row::rest).map BinaryWeightedPairRow.arc
      | some hit => hit ∈ row::rest ∧ hit.arc = key) ∧
        (if found.1 then _ else _ : Option (BinaryWeightedPairRow V) × ℕ).2 ≤ 2+(rest.length+1)*(10*labels+22)
    by_cases sameKey : key = row.arc
    · have matched : found.1 = true := by rw [value]; simp [sameKey]
      rw [matched]
      simp only [ite_true]
      refine ⟨⟨List.mem_cons_self,sameKey.symm⟩,?_⟩
      change found.2+5 ≤ 2+(rest.length+1)*(10*labels+22)
      rw [Nat.add_mul,Nat.one_mul]
      omega
    · have missed : found.1 = false := by rw [value]; simp [sameKey]
      rw [missed]
      simp only [Bool.false_eq_true,ite_false]
      constructor
      · change (match lower.1 with
          | none => key ∉ rest.map BinaryWeightedPairRow.arc
          | some hit => hit ∈ rest ∧ hit.arc = key) at tail
        cases result : lower.1 with
        | none => simp [result,List.map_cons,sameKey] at tail ⊢; exact tail
        | some hit =>
          rw [result] at tail
          exact ⟨List.mem_cons_of_mem _ tail.1,tail.2⟩
      · change found.2+lower.2+6 ≤ 2+(rest.length+1)*(10*labels+22)
        rw [Nat.add_mul,Nat.one_mul]
        omega

/-- Read the matching row and decode its already clipped capacity. -/
def binaryWeightedUnitsAtWithWork {V : Type*} (query : List Bool × List Bool)
    (free : List (List Bool × List Bool)) (ceiling : List Bool)
    (width supply : ℕ) (rows : List (BinaryWeightedPairRow V)) : ℕ × ℕ :=
  let found := findBinaryWeightedPairWithWork query rows
  match found.1 with
  | none => (0,found.2+3)
  | some row =>
    let capacity := binaryWeightedCapacityAtWithWork free ceiling supply row
    let decoded := decodeBinaryNatWithWork width capacity.1
    (decoded.1,found.2+capacity.2+decoded.2+5)

def binaryWeightedUnitsAtWorkBudget (rows free labels cost amount width supply : ℕ) : ℕ :=
  (2+rows*(10*labels+22))+binaryWeightedCapacityAtWorkBudget free labels cost amount supply+
    (2+width*(2*(width+1)+5))+5

/-- A complete represented table returns the exact clipped capacity for
each queried key. Charge the label scan, capacity operation and decoding. -/
theorem binaryWeightedUnitsAtWithWork_spec {V : Type*} [LinearOrder V]
    (edges : Arcs V) (weight charges : V × V → ℕ) (positive : ∀ e ∈ edges, 0 < weight e)
    (free : List (V × V)) (source target : V) (supply : ℕ) (ceiling : List Bool)
    (ceilingValue : binaryWordValue ceiling = supply) (code : V → List Bool)
    (injective : Function.Injective code) (labels costWidth amountWidth width : ℕ)
    (bounded : ∀ v, (code v).length ≤ labels) (wide : max ceiling.length supply ≤ width)
    (rows : List (BinaryWeightedPairRow V)) (key : V × V) (complete : key ∈ rows.map BinaryWeightedPairRow.arc)
    (encoded : ∀ row ∈ rows, row.Encodes edges weight charges code costWidth amountWidth) :
    let demand : WeightedNetworkDemand V := ⟨free.toFinset,source,target⟩
    let out := binaryWeightedUnitsAtWithWork (code key.1,code key.2) (binaryEncodeArcs code free) ceiling width supply rows
    (out.1 : ℤ) = min (weightedNetworkCapacity edges demand weight charges supply key) (supply : ℤ) ∧
    out.2 ≤ binaryWeightedUnitsAtWorkBudget rows.length free.length labels costWidth amountWidth width supply := by
  let found := findBinaryWeightedPairWithWork (code key.1,code key.2) rows
  obtain ⟨looked,lookWork⟩ := findBinaryWeightedPairWithWork_spec code injective labels bounded key rows
    (fun row h => (encoded row h).1)
  change (match found.1 with
    | none => key ∉ rows.map BinaryWeightedPairRow.arc
    | some hit => hit ∈ rows ∧ hit.arc = key) at looked
  change found.2 ≤ _ at lookWork
  cases hit : found.1 with
  | none => rw [hit] at looked; exact (looked complete).elim
  | some row =>
    rw [hit] at looked
    obtain ⟨present,correct⟩ := looked
    let capacity := binaryWeightedCapacityAtWithWork (binaryEncodeArcs code free) ceiling supply row
    obtain ⟨value,length,buildWork⟩ := binaryWeightedCapacityAtWithWork_spec edges weight charges positive free source target
      supply ceiling ceilingValue code injective labels costWidth amountWidth bounded row (encoded row present)
    change capacity.1.length ≤ max ceiling.length supply at length
    have decodeWork : (decodeBinaryNatWithWork width capacity.1).2 ≤ 2+width*(2*(width+1)+5) := by
      rw [decodeBinaryNatWithWork_spec]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (length.trans wide)) 2
    unfold binaryWeightedUnitsAtWithWork
    dsimp only at ⊢
    rw [show (findBinaryWeightedPairWithWork (code key.1,code key.2) rows).1 = some row from hit]
    refine ⟨?_,?_⟩
    · change ((decodeBinaryNatWithWork width capacity.1).1 : ℤ) = _
      rw [decodeBinaryNatWithWork_spec,← correct]
      exact value
    · change found.2+capacity.2+(decodeBinaryNatWithWork width capacity.1).2+5 ≤ _
      exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add lookWork buildWork) decodeWork) 5

/-- The tier already caps its dyadic capacities. A larger clip on the input
units leaves every ancestor cutoff unchanged. -/
theorem historyCutoff_clip_units {V : Type*} [DecidableEq V] [Fintype V] {h : ℕ}
    (sampleTier tier limit : ℕ) (large : 2^tier ≤ limit) (units : HeightNode V h → ℕ) (v : HeightNode V h) :
    historyCutoff sampleTier tier (fun u => min (units u) limit) v = historyCutoff sampleTier tier units v := by
  have capped (u : HeightNode V h) :
      rootCappedCapacity tier (fun node => min (units node) limit) u = rootCappedCapacity tier units u := by
    unfold rootCappedCapacity
    dsimp only
    by_cases small : units u ≤ limit
    · rw [min_eq_left small]
    · have more : limit ≤ units u := (Nat.lt_of_not_ge small).le
      have atClip := large.trans (dyadicCapacity_bounds limit).1
      have atUnit := atClip.trans (dyadicCapacity_mono more)
      rw [min_eq_right more,min_eq_left atClip,min_eq_left atUnit]
  have ancestors (u : HeightNode V h) :
      historyCapacityUnits tier (fun node => min (units node) limit) u = historyCapacityUnits tier units u := by
    unfold historyCapacityUnits
    rw [funext capped]
  unfold historyCutoff
  simp only [ancestors]

end OnlineReachabilityPreservers
