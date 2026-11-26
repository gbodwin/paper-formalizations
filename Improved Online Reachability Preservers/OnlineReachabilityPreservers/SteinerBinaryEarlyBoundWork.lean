import OnlineReachabilityPreservers.SteinerBinaryEarlyWork

/-! Bound the recorded binary early work uniformly by the trace length. -/

namespace OnlineReachabilityPreservers

open Finset

private theorem binaryWeightedNetworkTraceWorkBudget_mono_requests
    (n arcs rows free labels cost remainder power amount cap supply fuel : ℕ) :
    Monotone (binaryWeightedNetworkTraceWorkBudget n arcs rows free labels cost remainder power amount cap supply fuel) := by
  intro p q shorter
  have updates : p*fuel ≤ q*fuel := Nat.mul_le_mul_right _ shorter
  have amountLe : amount+(p*fuel)*(power+p*fuel+1) ≤ amount+(q*fuel)*(power+q*fuel+1) := by gcongr
  have loop := binaryWeightedCoverLoopWorkBudget_le n arcs rows labels cost cap supply fuel
    (le_refl free) (Nat.add_le_add_left updates remainder) (Nat.add_le_add_left updates power) amountLe
  unfold binaryWeightedNetworkTraceWorkBudget
  exact Nat.add_le_add_left (Nat.mul_le_mul shorter
    (Nat.add_le_add_right (Nat.add_le_add_right loop (5*fuel)) 10)) 2

private theorem binaryWeightedNetworkFromZeroWorkBudget_mono_requests
    (depth edges keys free labels width costRead labelRead scale fuel : ℕ) :
    Monotone (binaryWeightedNetworkFromZeroWorkBudget depth edges keys free labels width costRead labelRead scale fuel) := by
  intro p q shorter
  have encode : binaryWeightedRequestEncodingWorkBudget p free labelRead ≤
      binaryWeightedRequestEncodingWorkBudget q free labelRead := by
    unfold binaryWeightedRequestEncodingWorkBudget
    gcongr
  have trace := binaryWeightedNetworkTraceWorkBudget_mono_requests
    depth edges keys free labels width 0 1 width scale.size scale fuel shorter
  unfold binaryWeightedNetworkFromZeroWorkBudget
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add_left encode _) trace) 9

private theorem binaryForestRoundAdditionalWorkBudget_mono_amount
    (h vertices keys free labels cost scale trials links readFee : ℕ) :
    Monotone (fun amount => binaryForestRoundAdditionalWorkBudget h vertices keys free labels cost amount scale trials links readFee) := by
  intro amount more wider
  let W := 10*h+8*readFee+39
  let L := heightNodeIndexWordBudget h 1+boundedNatToBinaryWorkBudget labels+23
  let U := fun width => 2*L+binaryWeightedUnitsAtWorkBudget keys free labels cost width (max scale.size scale) scale+8
  have arithmetic := binaryCeilingDivWorkBudget_mono_widths wider (le_refl cost) 0 0 scale
  have units : U amount ≤ U more := by
    unfold U binaryWeightedUnitsAtWorkBudget binaryWeightedCapacityAtWorkBudget
    gcongr
  have tier := forestTierArithmeticWordBudget_le (h := h) (le_refl scale) units
  have roundWork : forestUnitTrialRowsWordBudget h scale trials links W (U amount) ≤
      forestUnitTrialRowsWordBudget h scale trials links W (U more) := by
    unfold forestUnitTrialRowsWordBudget
    dsimp only
    gcongr
  unfold binaryForestRoundAdditionalWorkBudget
  exact Nat.add_le_add_right (Nat.add_le_add_left roundWork _) 11

/-- The work allowance of the finite binary fractional forest, evaluated
from the prepared dimensions and the number of requests. -/
def binaryForestFractionalWorkBudgetForLength (n h paid free readFee scale fuel p : ℕ) : ℕ :=
  let rows := finForestNetworkRowsWithWordWork n h
  let labels := binaryFinForestNetworkLabelsWithWork n h
  (finForestNetworkPairKeysWordPolynomial n h+3)+(5*h+7*labels.count+13)+(7*n+3)+
    forestWeightedRequestsWorkBudget h rows.vertices.length rows.keys.length free p+
    binaryWeightedNetworkFromZeroWorkBudget labels.count paid rows.keys.length rows.keys.length labels.width n.size
      (12*paid+10*h+8*readFee+53) (heightNodeIndexWordBudget h 1+boundedNatToBinaryWorkBudget labels.width+23)
      scale fuel p+11

private theorem binaryForestFractionalWorkBudgetForLength_mono (n h paid free readFee scale fuel : ℕ) :
    Monotone (binaryForestFractionalWorkBudgetForLength n h paid free readFee scale fuel) := by
  intro p q shorter
  let rows := finForestNetworkRowsWithWordWork n h
  let labels := binaryFinForestNetworkLabelsWithWork n h
  have requests : forestWeightedRequestsWorkBudget h rows.vertices.length rows.keys.length free p ≤
      forestWeightedRequestsWorkBudget h rows.vertices.length rows.keys.length free q := by
    unfold forestWeightedRequestsWorkBudget
    gcongr
  have trace := binaryWeightedNetworkFromZeroWorkBudget_mono_requests labels.count paid rows.keys.length rows.keys.length
    labels.width n.size (12*paid+10*h+8*readFee+53)
    (heightNodeIndexWordBudget h 1+boundedNatToBinaryWorkBudget labels.width+23) scale fuel shorter
  unfold binaryForestFractionalWorkBudgetForLength
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add_left requests _) trace) 11

local instance binaryEarlyBoundHeightDecidableEq {n h : ℕ} : DecidableEq (HeightForestVertex (Fin n) h) :=
  (inferInstance : LinearOrder (HeightForestVertex (Fin n) h)).toDecidableEq

local instance binaryEarlyBoundNetworkDecidableEq {n h : ℕ} : DecidableEq (ForestNetworkVertex (Fin n) h) :=
  (inferInstance : LinearOrder (ForestNetworkVertex (Fin n) h)).toDecidableEq

/-- Uniform early metric allowance in the trace length. Compute the cost
from the prepared dimensions, the reference scale and fuel, and reader budgets. -/
def binaryEarlyMetricWorkBudgetForLength {n h : ℕ} (G : Arcs (Fin n))
    (paid free : Arcs (ForestNetworkVertex (Fin n) h)) (freeRows readFee seedFee p : ℕ) : ℕ :=
  let labels := binaryFinForestNetworkLabelsWithWork n h
  let keys := (finForestNetworkRowsWithWordWork n h).keys.length
  let weight := forestNetworkWeight G (height := h)
  let fuel := weightedCoverFuel paid weight
  let updates := p*fuel
  let scale := forestScale G h
  let trials := earlyTrialCount (Fin n) h
  let links := (heightForest G h).card
  binaryForestFractionalWorkBudgetForLength n h paid.card free.card readFee (weightedCoverScale paid weight) fuel p+
    binaryForestRoundAdditionalWorkBudget h labels.count keys freeRows labels.width n.size
      (n.size+updates*(1+updates+1)) scale trials links readFee+
    trials*(links*((scale.log2+1)*((h+2)*seedFee)))+5

theorem binaryEarlyMetricWorkBudgetForLength_mono {n h : ℕ} (G : Arcs (Fin n))
    (paid free : Arcs (ForestNetworkVertex (Fin n) h)) (freeRows readFee seedFee : ℕ) :
    Monotone (binaryEarlyMetricWorkBudgetForLength G paid free freeRows readFee seedFee) := by
  intro p q shorter
  let labels := binaryFinForestNetworkLabelsWithWork n h
  let keys := (finForestNetworkRowsWithWordWork n h).keys.length
  let weight := forestNetworkWeight G (height := h)
  let fuel := weightedCoverFuel paid weight
  have updates : p*fuel ≤ q*fuel := Nat.mul_le_mul_right _ shorter
  have amount : n.size+(p*fuel)*(1+p*fuel+1) ≤ n.size+(q*fuel)*(1+q*fuel+1) := by gcongr
  have fractional := binaryForestFractionalWorkBudgetForLength_mono
    n h paid.card free.card readFee (weightedCoverScale paid weight) fuel shorter
  have rounding := binaryForestRoundAdditionalWorkBudget_mono_amount h labels.count keys freeRows labels.width
    n.size (forestScale G h) (earlyTrialCount (Fin n) h) (heightForest G h).card readFee amount
  unfold binaryEarlyMetricWorkBudgetForLength
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add fractional rounding) _) 5

/-- Evaluate the binary metric allowance from the exact forest classes. -/
def finSteinerBinaryEarlyMetricWorkBudget {n : ℕ} (G : Arcs (Fin n)) (h seedFee p : ℕ) : ℕ :=
  let paid := forestNetworkPriced G (heightForest G h)
  let free := forestNetworkZero G h
  binaryEarlyMetricWorkBudgetForLength G paid free free.card (n^2) seedFee p

theorem finSteinerBinaryEarlyMetricWorkBudget_mono {n : ℕ} (G : Arcs (Fin n)) (h seedFee : ℕ) :
    Monotone (finSteinerBinaryEarlyMetricWorkBudget G h seedFee) :=
  binaryEarlyMetricWorkBudgetForLength_mono G (forestNetworkPriced G (heightForest G h))
    (forestNetworkZero G h) (forestNetworkZero G h).card (n^2) seedFee

/-- Bound all binary early prefix charges by the dimensions of the input
and a single allowance evaluated at the full demand count. -/
theorem binaryEarlyRoundedGraphWithWork_tally_le {n h : ℕ} (G : Arcs (Fin n))
    (links : {es : List (HeightForestVertex (Fin n) h × HeightForestVertex (Fin n) h) // es.Nodup})
    (linksExact : links.val.toFinset = heightForest G h)
    (paid free : Arcs (ForestNetworkVertex (Fin n) h))
    (paidExact : paid = forestNetworkPriced G (heightForest G h)) (freeExact : free = forestNetworkZero G h)
    (freeRows : List (ForestNetworkVertex (Fin n) h × ForestNetworkVertex (Fin n) h))
    (freeAsSet : freeRows.toFinset = free)
    (read : Fin n × Fin n → ℕ × ℕ) (readFee : ℕ)
    (readExact : ∀ e, (read e).1 = hops G e.1 e.2) (readWork : ∀ e, (read e).2 ≤ readFee)
    (samples : ForestTrialArrayWithSeedWork (Fin n) h (forestScale G h) (earlyTrialCount (Fin n) h))
    (seedFee : ℕ) (seedWork : ∀ i, forestSampleWorkBound (samples i) seedFee) (D : List (Fin n × Fin n)) :
    let out := binaryEarlyRoundedGraphWithWork G links paid free freeRows read (forestScale G h)
      (earlyTrialCount (Fin n) h) samples D
    let B := binaryEarlyMetricWorkBudgetForLength G paid free freeRows.length readFee seedFee D.length
    out.2.2 ≤ (D.length+1)^2*B := by
  let budget := binaryEarlyMetricWorkBudget G paid free freeRows.length readFee seedFee read
  let allowance := binaryEarlyMetricWorkBudgetForLength G paid free freeRows.length readFee seedFee
  let B := allowance D.length
  let prefixes := D.inits.toFinset
  have each (P : List (Fin n × Fin n)) (inside : P ∈ prefixes) : budget P ≤ B := by
    have frac := (binaryForestFractionalWithWork_refines G h paid free paidExact freeExact read readFee
      readExact readWork P).2.2.2
    have cost : budget P ≤ allowance P.length := by
      dsimp only [budget,allowance,binaryEarlyMetricWorkBudget,binaryEarlyMetricWorkBudgetForLength]
      exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right frac _) _) 5
    have shorter := ((List.mem_inits _ _).mp (List.mem_toFinset.mp inside)).length_le
    exact cost.trans (binaryEarlyMetricWorkBudgetForLength_mono G paid free freeRows.length readFee seedFee shorter)
  have count : prefixes.card ≤ D.length+1 := (List.toFinset_card_le _).trans_eq (List.length_inits _)
  have sum : (∑ P ∈ prefixes, budget P) ≤ (D.length+1)*B := calc
    _ ≤ ∑ _ ∈ prefixes, B := sum_le_sum each
    _ = prefixes.card*B := by simp
    _ ≤ _ := Nat.mul_le_mul_right B count
  have actual := (binaryEarlyRoundedGraphWithWork_refines G links linksExact paid free paidExact freeExact freeRows
    freeAsSet read readFee readExact readWork samples seedFee seedWork D).2.2
  exact actual.trans ((Nat.mul_le_mul_left (D.length+1) sum).trans_eq (by rw [pow_two,Nat.mul_assoc]))

end OnlineReachabilityPreservers
