import OnlineReachabilityPreservers.SteinerBinaryWeightedLoopWork

/-! Reuse the weighted pair table across requests with distinct free attachments. -/

namespace OnlineReachabilityPreservers

/-- A weighted request with its free arcs in the supplied storage order. -/
structure WeightedNetworkRequestRows (V : Type*) where
  free : List (V × V)
  source : V
  target : V

def WeightedNetworkRequestRows.reference {V : Type*} [DecidableEq V] (request : WeightedNetworkRequestRows V) :
    WeightedNetworkDemand V := ⟨request.free.toFinset,request.source,request.target⟩

structure BinaryWeightedRequestRows where
  free : List (List Bool × List Bool)
  source : List Bool
  target : List Bool

def WeightedNetworkRequestRows.encode {V : Type*} (code : V → List Bool) (request : WeightedNetworkRequestRows V) :
    BinaryWeightedRequestRows := ⟨binaryEncodeArcs code request.free,code request.source,code request.target⟩

private def appendWeightedCutsWithWork {A : Type*} (suffix : List A) : List A → List A × ℕ
  | [] => (suffix,2)
  | cut::rest =>
    let more := appendWeightedCutsWithWork suffix rest
    (cut::more.1,more.2+5)

private theorem appendWeightedCutsWithWork_spec {A : Type*} (first suffix : List A) :
    appendWeightedCutsWithWork suffix first = (first++suffix,2+5*first.length) := by
  induction first with
  | nil => rfl
  | cons cut rest ih =>
    simp only [appendWeightedCutsWithWork,ih,List.cons_append,List.length_cons]
    congr 1

/-- Use the final table from each request as the initial table for the
next, replacing the free attachments at each arrival. -/
def binaryWeightedNetworkTraceWithWork {V : Type*} (arcs : List (List Bool × List Bool)) (ceiling : List Bool)
    (depth supply fuel : ℕ) : List BinaryWeightedRequestRows → List (BinaryWeightedPairRow V) →
    (List (BinaryWeightedPairRow V) × List (List (List Bool × List Bool))) × ℕ
  | [], rows => ((rows,[]),2)
  | d::rest, rows =>
    let first := binaryWeightedCoverLoopWithWork arcs d.free ceiling d.source d.target depth supply fuel rows
    let tail := binaryWeightedNetworkTraceWithWork arcs ceiling depth supply fuel rest first.1.1
    let history := appendWeightedCutsWithWork tail.1.2 first.1.2
    ((tail.1.1,history.1),first.2+tail.2+history.2+8)

def binaryWeightedNetworkTraceWorkBudget (n arcs rows free labels cost remainder power amount cap supply fuel requests : ℕ) : ℕ :=
  let total := requests*fuel
  2+requests*(binaryWeightedCoverLoopWorkBudget n arcs rows free labels cost (remainder+total) (power+total)
    (amount+total*(power+total+1)) cap supply fuel+5*fuel+10)

private theorem weightedCoverLoop_history_length_le {A : Type*} [DecidableEq A]
    (search : (A → ℕ) → Option (Finset A)) (fuel : ℕ) (charges : A → ℕ) :
    (weightedCoverLoop search fuel charges).2.length ≤ fuel := by
  induction fuel generalizing charges with
  | zero => simp [weightedCoverLoop]
  | succ fuel ih =>
    cases found : search charges with
    | none => simp [weightedCoverLoop,found]
    | some cut => simpa [weightedCoverLoop,found] using Nat.succ_le_succ (ih (chargeWeightedCut cut charges))

private theorem weightedAmountAfter_two (amount power first tail : ℕ) :
    amount+first*(power+first+1)+tail*(power+first+tail+1) ≤ amount+(first+tail)*(power+(first+tail)+1) := by
  have ordered : power+first+1 ≤ power+(first+tail)+1 := by omega
  have growth := Nat.mul_le_mul_left first ordered
  rw [Nat.add_mul,show power+first+tail+1 = power+(first+tail)+1 by omega]
  omega

variable {V : Type*} [LinearOrder V] [Fintype V]

set_option maxHeartbeats 1200000 in
/-- The same pair table represents the reference charges throughout the
weighted trace. Every cut is returned in chronological order using the
request's own free arcs. The bound uses the total supplied fuel. -/
theorem binaryWeightedNetworkTraceWithWork_refines (arcs : List (V × V)) (simple : arcs.Nodup)
    (weight charges : V × V → ℕ) (positive : ∀ e ∈ arcs.toFinset, 0 < weight e)
    (supply fuel : ℕ) (supplyExact : supply = weightedCoverScale arcs.toFinset weight)
    (fuelExact : fuel = weightedCoverFuel arcs.toFinset weight)
    (ceiling : List Bool) (supplyWord : binaryWordValue ceiling = supply) (code : V → List Bool)
    (injective : Function.Injective code) (labels costWidth remainderWidth powerWidth amountWidth freeLimit : ℕ)
    (bounded : ∀ v, (code v).length ≤ labels) (rows : List (BinaryWeightedPairRow V))
    (complete : ∀ e, e ∈ rows.map BinaryWeightedPairRow.arc)
    (encoded : ∀ row ∈ rows, row.Encodes arcs.toFinset weight charges code costWidth amountWidth)
    (widths : ∀ row ∈ rows, row.ChargeWidths remainderWidth powerWidth)
    (requests : List (WeightedNetworkRequestRows V)) (short : ∀ d ∈ requests, d.free.length ≤ freeLimit) :
    let G := arcs.toFinset
    let total := requests.length*fuel
    let ref := weightedNetworkRun G weight (requests.map WeightedNetworkRequestRows.reference) charges
    let out := binaryWeightedNetworkTraceWithWork (binaryEncodeArcs code arcs) ceiling (Fintype.card V) supply fuel
      (requests.map (WeightedNetworkRequestRows.encode code)) rows
    out.1.1.map BinaryWeightedPairRow.arc = rows.map BinaryWeightedPairRow.arc ∧
    (∀ row ∈ out.1.1, row.Encodes G weight ref.1 code costWidth (amountWidth+total*(powerWidth+total+1))) ∧
    (∀ row ∈ out.1.1, row.ChargeWidths (remainderWidth+total) (powerWidth+total)) ∧
    (∃ cuts : List (List (V × V)), out.1.2 = cuts.map (binaryEncodeArcs code) ∧ cuts.map List.toFinset = ref.2) ∧
    out.2 ≤ binaryWeightedNetworkTraceWorkBudget (Fintype.card V) arcs.length rows.length freeLimit labels costWidth
      remainderWidth powerWidth amountWidth ceiling.length supply fuel requests.length := by
  let G := arcs.toFinset
  let depth := Fintype.card V
  let paidBits := binaryEncodeArcs code arcs
  induction requests generalizing charges rows remainderWidth powerWidth amountWidth with
  | nil =>
    refine ⟨rfl,?_,?_,⟨[],rfl,rfl⟩,?_⟩
    · simpa [binaryWeightedNetworkTraceWithWork,weightedNetworkRun] using encoded
    · simpa [binaryWeightedNetworkTraceWithWork] using widths
    · simp [binaryWeightedNetworkTraceWithWork,binaryWeightedNetworkTraceWorkBudget]
  | cons d rest ih =>
    let first := binaryWeightedCoverLoopWithWork paidBits (binaryEncodeArcs code d.free) ceiling (code d.source)
      (code d.target) depth supply fuel rows
    let next := weightedNetworkStep G weight d.reference charges
    let tailFuel := rest.length*fuel
    let total := (rest.length+1)*fuel
    let R := remainderWidth+total
    let P := powerWidth+total
    let A := amountWidth+total*(powerWidth+total+1)
    let firstAmount := amountWidth+fuel*(powerWidth+fuel+1)
    let fee := binaryWeightedCoverLoopWorkBudget depth arcs.length rows.length freeLimit labels costWidth R P A ceiling.length supply fuel
    let tail := binaryWeightedNetworkTraceWithWork paidBits ceiling depth supply fuel
      (rest.map (WeightedNetworkRequestRows.encode code)) first.1.1
    obtain ⟨keys,stored,kept,⟨front,frontLabels,frontExact⟩,firstCost⟩ := binaryWeightedCoverLoopWithWork_refines
      arcs d.free d.source d.target supply fuel simple weight charges positive ceiling supplyWord code injective labels
      costWidth remainderWidth powerWidth amountWidth bounded rows complete encoded widths
    have refEq : weightedCoverLoop (weightedNetworkViolation G d.reference weight supply) fuel charges = next := by
      rw [supplyExact,fuelExact]
      rfl
    change ∀ row ∈ first.1.1, row.Encodes G weight
      (weightedCoverLoop (weightedNetworkViolation G d.reference weight supply) fuel charges).1 code costWidth firstAmount at stored
    change front.map List.toFinset = (weightedCoverLoop (weightedNetworkViolation G d.reference weight supply) fuel charges).2 at frontExact
    rw [refEq] at stored frontExact
    change first.1.1.map BinaryWeightedPairRow.arc = rows.map BinaryWeightedPairRow.arc at keys
    have nextComplete : ∀ e, e ∈ first.1.1.map BinaryWeightedPairRow.arc := by intro e; rw [keys]; exact complete e
    have nextCount : first.1.1.length = rows.length := by simpa only [List.length_map] using congrArg List.length keys
    obtain ⟨same,ending,lastWidths,⟨back,backLabels,backExact⟩,lastCost⟩ :=
      ih next.1 (remainderWidth+fuel) (powerWidth+fuel) firstAmount first.1.1 nextComplete stored kept
        (fun r rd => short r (List.mem_cons_of_mem _ rd))
    let priorEnd := weightedNetworkRun G weight (rest.map WeightedNetworkRequestRows.reference) next.1
    have totalSplit : total = fuel+tailFuel := by
      dsimp only [total,tailFuel]
      rw [Nat.add_mul,Nat.one_mul,Nat.add_comm]
    have enoughR : remainderWidth+fuel+tailFuel = R := by dsimp only [R]; omega
    have enoughP : powerWidth+fuel+tailFuel = P := by dsimp only [P]; omega
    have enoughA : firstAmount+tailFuel*(powerWidth+fuel+tailFuel+1) ≤ A := by
      dsimp only [firstAmount,A]
      rw [totalSplit]
      exact weightedAmountAfter_two _ _ _ _
    have widerA : firstAmount+tailFuel*(P+1) ≤ A := by rw [← enoughP]; exact enoughA
    have callFuel : fuel ≤ total := by rw [totalSplit]; exact Nat.le_add_right _ _
    have firstFee : first.2 ≤ fee := by
      apply firstCost.trans
      apply binaryWeightedCoverLoopWorkBudget_le
      · exact short d List.mem_cons_self
      · exact Nat.le_add_right _ _
      · exact Nat.le_add_right _ _
      · exact Nat.le_add_right _ _
    have lastFee : tail.2 ≤ 2+rest.length*(fee+5*fuel+10) := by
      change tail.2 ≤ _ at lastCost
      unfold binaryWeightedNetworkTraceWorkBudget at lastCost
      change tail.2 ≤ 2+rest.length*(binaryWeightedCoverLoopWorkBudget depth arcs.length first.1.1.length freeLimit labels
        costWidth (remainderWidth+fuel+tailFuel) (powerWidth+fuel+tailFuel) (firstAmount+tailFuel*(powerWidth+fuel+tailFuel+1))
        ceiling.length supply fuel+5*fuel+10) at lastCost
      rw [nextCount,enoughR,enoughP] at lastCost
      have allowed : binaryWeightedCoverLoopWorkBudget depth arcs.length rows.length freeLimit labels costWidth R P
          (firstAmount+tailFuel*(P+1)) ceiling.length supply fuel ≤ fee :=
        binaryWeightedCoverLoopWorkBudget_le depth arcs.length rows.length labels costWidth ceiling.length supply fuel
          le_rfl le_rfl le_rfl widerA
      exact lastCost.trans (by gcongr)
    have enoughCuts : first.1.2.length ≤ fuel := by
      have exactCount : front.length = next.2.length := by
        simpa only [List.length_map] using congrArg List.length frontExact
      have bound := weightedCoverLoop_history_length_le (weightedNetworkViolation G d.reference weight supply) fuel charges
      rw [refEq] at bound
      change first.1.2 = front.map (binaryEncodeArcs code) at frontLabels
      rw [frontLabels,List.length_map,exactCount]
      exact bound
    let history := appendWeightedCutsWithWork tail.1.2 first.1.2
    have joined := appendWeightedCutsWithWork_spec first.1.2 tail.1.2
    have appendFee : history.2 ≤ 2+5*fuel := by
      change (appendWeightedCutsWithWork tail.1.2 first.1.2).2 ≤ _
      rw [joined]
      dsimp only
      gcongr
    change tail.1.1.map BinaryWeightedPairRow.arc = _ at same
    change ∀ row ∈ tail.1.1, row.Encodes G weight priorEnd.1 code costWidth
      (firstAmount+tailFuel*(powerWidth+fuel+tailFuel+1)) at ending
    change ∀ row ∈ tail.1.1, row.ChargeWidths (remainderWidth+fuel+tailFuel) (powerWidth+fuel+tailFuel) at lastWidths
    refine ⟨same.trans keys,?_,?_,⟨front++back,?_,?_⟩,?_⟩
    · intro row present
      exact BinaryWeightedPairRow.amount_le (ending row present) enoughA
    · intro row present
      exact BinaryWeightedPairRow.chargeWidths_le (lastWidths row present) (le_of_eq enoughR) (le_of_eq enoughP)
    · change (appendWeightedCutsWithWork tail.1.2 first.1.2).1 = _
      change tail.1.2 = _ at backLabels
      change first.1.2 = _ at frontLabels
      rw [joined,List.map_append,frontLabels,backLabels]
    · change (front++back).map List.toFinset = next.2++priorEnd.2
      rw [List.map_append,frontExact,backExact]
    · change first.2+tail.2+history.2+8 ≤ 2+(rest.length+1)*(fee+5*fuel+10)
      rw [Nat.add_mul,Nat.one_mul]
      omega

end OnlineReachabilityPreservers
