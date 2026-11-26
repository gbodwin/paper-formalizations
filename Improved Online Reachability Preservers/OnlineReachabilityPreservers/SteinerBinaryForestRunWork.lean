import OnlineReachabilityPreservers.SteinerBinaryForestFractionalWork
import OnlineReachabilityPreservers.SteinerBinaryForestRoundingWork

/-! Round the same binary forest state produced by a typed request trace. -/

namespace OnlineReachabilityPreservers

open Finset

local instance binaryForestRunHeightDecidableEq {n h : ℕ} : DecidableEq (HeightForestVertex (Fin n) h) :=
  (inferInstance : LinearOrder (HeightForestVertex (Fin n) h)).toDecidableEq

local instance binaryForestRunNetworkDecidableEq {n h : ℕ} : DecidableEq (ForestNetworkVertex (Fin n) h) :=
  (inferInstance : LinearOrder (ForestNetworkVertex (Fin n) h)).toDecidableEq

/-- Compute the binary fractional forest, encode the permanent free arcs
once, and round from the resulting paid rows. -/
def binaryForestRoundWithWork {n h : ℕ}
    (links : {es : List (HeightForestVertex (Fin n) h × HeightForestVertex (Fin n) h) // es.Nodup})
    (paid free : Arcs (ForestNetworkVertex (Fin n) h))
    (freeRows : List (ForestNetworkVertex (Fin n) h × ForestNetworkVertex (Fin n) h))
    (read : Fin n × Fin n → ℕ × ℕ) (scale trials : ℕ)
    (sample : ForestTrialArrayWithSeedWork (Fin n) h scale trials) (D : List (Fin n × Fin n)) :
    Arcs (HeightForestVertex (Fin n) h) × ℕ × ℕ :=
  let fractional := binaryForestFractionalWithWork h paid free read D
  let labels := binaryFinForestNetworkLabelsWithWork n h
  let zero := encodeWeightedArcsWithWork labels.read freeRows
  let width := bitLengthWithWork scale
  let ceiling := encodeBoundedNatWithBinaryWork scale width.1
  let rounded := roundedForestTrialsFromBinaryStateWithWork links (forestDistanceWeightWithWordWork read)
    labels.read zero.1 ceiling.1 (max width.1 scale) scale trials fractional.1.1 sample
  (rounded.1,fractional.2+labels.work+zero.2+width.2+ceiling.2+rounded.2.1+11,rounded.2.2)

/-- Work beyond the weighted trace, with the input widths used by the
rounding reader and the two measured encodings. -/
def binaryForestRoundAdditionalWorkBudget (h vertices keys free labels cost amount scale trials links readFee : ℕ) : ℕ :=
  let labelFee := heightNodeIndexWordBudget h 1+boundedNatToBinaryWorkBudget labels+23
  let weightFee := 10*h+8*readFee+39
  let unitFee := 2*labelFee+binaryWeightedUnitsAtWorkBudget keys free labels cost amount (max scale.size scale) scale+8
  (5*h+7*vertices+13)+(2+free*(2*labelFee+6))+(7*scale+3)+boundedNatToBinaryWorkBudget scale.size+
    forestUnitTrialRowsWordBudget h scale trials links weightFee unitFee+11

set_option maxHeartbeats 900000 in
/-- The recorded unit reader uses the actual output of the binary weighted
trace. The fixed trial samples produce the exact reference rounded forest. -/
theorem binaryForestRoundWithWork_refines {n h : ℕ} (G : Arcs (Fin n))
    (links : {es : List (HeightForestVertex (Fin n) h × HeightForestVertex (Fin n) h) // es.Nodup})
    (linksExact : links.val.toFinset = heightForest G h)
    (paid free : Arcs (ForestNetworkVertex (Fin n) h))
    (paidExact : paid = forestNetworkPriced G (heightForest G h)) (freeExact : free = forestNetworkZero G h)
    (freeRows : List (ForestNetworkVertex (Fin n) h × ForestNetworkVertex (Fin n) h))
    (freeAsSet : freeRows.toFinset = free)
    (read : Fin n × Fin n → ℕ × ℕ) (readFee : ℕ)
    (readExact : ∀ e, (read e).1 = hops G e.1 e.2) (readWork : ∀ e, (read e).2 ≤ readFee)
    (scale trials : ℕ) (scalePos : 0 < scale)
    (sample : ForestTrialArrayWithSeedWork (Fin n) h scale trials) (seedFee : ℕ)
    (seedWork : ∀ i, forestSampleWorkBound (sample i) seedFee) (D : List (Fin n × Fin n)) :
    let out := binaryForestRoundWithWork links paid free freeRows read scale trials sample D
    let labels := binaryFinForestNetworkLabelsWithWork n h
    let fuel := weightedCoverFuel paid (forestNetworkWeight G)
    let updates := D.length*fuel
    let keys := (finForestNetworkRowsWithWordWork n h).keys
    out.1 = roundedForestTrials G (forestFractionalRun G h D).1 scale trials
      (fun i => forestRoundingSampleValues scale (sample i)) ∧
    out.2.1 ≤ (binaryForestFractionalWithWork h paid free read D).2+
      binaryForestRoundAdditionalWorkBudget h labels.count keys.length freeRows.length labels.width n.size
        (n.size+updates*(1+updates+1)) scale trials (heightForest G h).card readFee ∧
    out.2.2 ≤ trials*((heightForest G h).card*((scale.log2+1)*((h+2)*seedFee))) := by
  let fractional := binaryForestFractionalWithWork h paid free read D
  let labels := binaryFinForestNetworkLabelsWithWork n h
  let freeEncoding := encodeWeightedArcsWithWork labels.read freeRows
  let width := bitLengthWithWork scale
  let ceiling := encodeBoundedNatWithBinaryWork scale width.1
  let fuel := weightedCoverFuel paid (forestNetworkWeight G)
  let amount := n.size+(D.length*fuel)*(1+D.length*fuel+1)
  let keys := (finForestNetworkRowsWithWordWork n h).keys
  let labelFee := heightNodeIndexWordBudget h 1+boundedNatToBinaryWorkBudget labels.width+23
  let weightFee := 10*h+8*readFee+39
  let weight := forestDistanceWeightWithWordWork (h := h) read
  let rounds := roundedForestTrialsFromBinaryStateWithWork links weight labels.read freeEncoding.1 ceiling.1
    (max width.1 scale) scale trials fractional.1.1 sample
  obtain ⟨pairOrder,states,_,_⟩ := binaryForestFractionalWithWork_refines G h paid free paidExact freeExact read readFee
    readExact readWork D
  obtain ⟨_,_,_,injective,labelReads,labelSetup⟩ := binaryFinForestNetworkLabelsWithWork_spec n h
  obtain ⟨freeValue,freeFee⟩ := encodeWeightedArcsWithWork_spec labels.read labelFee (fun v => (labelReads v).2) freeRows
  have widthEq : width.1 = scale.size := (bitLengthWithWork_spec scale).1
  have widthFee : width.2 ≤ 7*scale+3 := bitLengthWork_le scale
  have fits : scale < 2^width.1 := by rw [widthEq]; exact Nat.lt_size_self scale
  obtain ⟨ceilingValue,ceilingWidth,ceilingFee⟩ := encodeBoundedNatWithBinaryWork_spec scale width.1 fits
  have weightBound (e : HeightForestVertex (Fin n) h × HeightForestVertex (Fin n) h) :=
    forestDistanceWeightWithWordWork_spec read readFee readWork e
  have metric (e : HeightForestVertex (Fin n) h × HeightForestVertex (Fin n) h) :
      (weight e).1 = heightForestWeight G e := (weightBound e).1.trans (readExact _)
  have allPairs : ∀ k, k ∈ fractional.1.1.map BinaryWeightedPairRow.arc := by
    change fractional.1.1.map BinaryWeightedPairRow.arc = keys at pairOrder
    rw [pairOrder]
    exact (finForestNetworkRowsWithWordWork_spec n h).2.2.2.2.1
  have paidState (row : BinaryWeightedPairRow (ForestNetworkVertex (Fin n) h)) (inside : row ∈ fractional.1.1) :
      row.Encodes (forestNetworkPriced G (heightForest G h)) (forestNetworkWeight G) (forestFractionalRun G h D).1
        (fun v => (labels.read v).1) n.size amount := by
    rw [← paidExact]
    exact (states row inside).1
  have wide : max ceiling.1.length scale ≤ max width.1 scale := by
    change ceiling.1.length = width.1 at ceilingWidth
    rw [ceilingWidth]
  obtain ⟨graph,work,reads⟩ := roundedForestTrialsFromBinaryStateWithWork_refines G links linksExact
    weight weightFee metric (fun e => (weightBound e).2) (forestFractionalRun G h D).1 freeRows
    (freeAsSet.trans freeExact) ceiling.1 (max width.1 scale) scale trials scalePos ceilingValue wide
    labels.read labelFee labels.width n.size amount injective (fun v => (labelReads v).1.le)
    (fun v => (labelReads v).2) fractional.1.1 allPairs paidState sample seedFee seedWork
  have original : rounds = roundedForestTrialsFromBinaryStateWithWork links weight labels.read
      (binaryEncodeArcs (fun v => (labels.read v).1) freeRows) ceiling.1 (max width.1 scale) scale trials
      fractional.1.1 sample := by
    dsimp only [rounds]
    rw [freeValue]
  rw [← original] at graph work reads
  refine ⟨graph,?_,reads⟩
  change fractional.2+labels.work+freeEncoding.2+width.2+ceiling.2+rounds.2.1+11 ≤ _
  have keyCount : fractional.1.1.length = keys.length := by
    have count := congrArg List.length pairOrder
    simpa only [List.length_map] using count
  rw [keyCount,widthEq] at work
  have ceilingWork : ceiling.2 ≤ boundedNatToBinaryWorkBudget scale.size := by
    change ceiling.2 ≤ boundedNatToBinaryWorkBudget width.1 at ceilingFee
    rwa [widthEq] at ceilingFee
  have extra : labels.work+freeEncoding.2+width.2+ceiling.2+rounds.2.1+11 ≤
      binaryForestRoundAdditionalWorkBudget h labels.count keys.length freeRows.length labels.width n.size
        amount scale trials (heightForest G h).card readFee :=
    Nat.add_le_add_right (Nat.add_le_add
      (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add labelSetup freeFee) widthFee) ceilingWork) work) 11
  calc
    fractional.2+labels.work+freeEncoding.2+width.2+ceiling.2+rounds.2.1+11 =
        fractional.2+(labels.work+freeEncoding.2+width.2+ceiling.2+rounds.2.1+11) := by ac_rfl
    _ ≤ _ := Nat.add_le_add_left extra fractional.2

end OnlineReachabilityPreservers
