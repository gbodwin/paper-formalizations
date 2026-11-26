import OnlineReachabilityPreservers.SteinerBinaryEarlyBoundWork

/-! Bound the early binary replay costs with common input size allowances. -/

namespace OnlineReachabilityPreservers

open Finset

private theorem binaryWeightedNetworkFromZeroWorkBudget_le_dimensions
    {depth depth' edges edges' keys keys' free free' labels labels' width width' costRead costRead'
      labelRead labelRead' scale scale' fuel fuel' : ℕ} (p : ℕ)
    (vertexCount : depth ≤ depth') (edgeCount : edges ≤ edges') (pairCount : keys ≤ keys')
    (freeCount : free ≤ free') (labelWidth : labels ≤ labels') (costWidth : width ≤ width')
    (costFee : costRead ≤ costRead') (labelFee : labelRead ≤ labelRead') (scales : scale ≤ scale')
    (updatesPerRequest : fuel ≤ fuel') :
    binaryWeightedNetworkFromZeroWorkBudget depth edges keys free labels width costRead labelRead scale fuel p ≤
      binaryWeightedNetworkFromZeroWorkBudget depth' edges' keys' free' labels' width' costRead' labelRead' scale' fuel' p := by
  have updates : p*fuel ≤ p*fuel' := Nat.mul_le_mul_left p updatesPerRequest
  have numerator : width+(p*fuel)*(1+p*fuel+1) ≤ width'+(p*fuel')*(1+p*fuel'+1) := by gcongr
  have scaleWidth := Nat.size_le_size scales
  have loop := binaryWeightedCoverLoopWorkBudget_le_dimensions vertexCount edgeCount pairCount freeCount
    labelWidth costWidth (Nat.add_le_add_left updates 0) (Nat.add_le_add_left updates 1) numerator
    scaleWidth scales updatesPerRequest
  unfold binaryWeightedNetworkFromZeroWorkBudget binaryWeightedNetworkTraceWorkBudget
    binaryWeightedRequestEncodingWorkBudget binaryWeightedInitialTableWorkBudget boundedNatToBinaryWorkBudget
  dsimp only
  gcongr

private theorem binaryForestRoundAdditionalWorkBudget_le_dimensions {h vertices vertices' keys keys' free free'
      labels labels' cost cost' amount amount' scale scale' trials trials' links links' readFee : ℕ}
    (vertexCount : vertices ≤ vertices') (keyCount : keys ≤ keys') (freeCount : free ≤ free')
    (labelWidth : labels ≤ labels') (costWidth : cost ≤ cost') (numerator : amount ≤ amount')
    (scales : scale ≤ scale') (trialCount : trials ≤ trials') (linkCount : links ≤ links') :
    binaryForestRoundAdditionalWorkBudget h vertices keys free labels cost amount scale trials links readFee ≤
      binaryForestRoundAdditionalWorkBudget h vertices' keys' free' labels' cost' amount' scale' trials' links' readFee := by
  let W := 10*h+8*readFee+39
  let labelFee := fun size => heightNodeIndexWordBudget h 1+boundedNatToBinaryWorkBudget size+23
  let U := fun rows freeRows labels cost amount scale =>
    2*labelFee labels+binaryWeightedUnitsAtWorkBudget rows freeRows labels cost amount (max scale.size scale) scale+8
  have scaleWidth := Nat.size_le_size scales
  have compareWidth := max_le_max scaleWidth scales
  have divCost := binaryCeilingDivWorkBudget_le numerator costWidth (le_refl 0) (le_refl 0) scales
  have units : U keys free labels cost amount scale ≤ U keys' free' labels' cost' amount' scale' := by
    unfold U labelFee binaryWeightedUnitsAtWorkBudget binaryWeightedCapacityAtWorkBudget boundedNatToBinaryWorkBudget
    gcongr
  have tier := forestTierArithmeticWordBudget_le (h := h) scales units
  have roundWork : forestUnitTrialRowsWordBudget h scale trials links W (U keys free labels cost amount scale) ≤
      forestUnitTrialRowsWordBudget h scale' trials' links' W (U keys' free' labels' cost' amount' scale') := by
    unfold forestUnitTrialRowsWordBudget
    dsimp only
    gcongr
  have encodes : boundedNatToBinaryWorkBudget scale.size ≤ boundedNatToBinaryWorkBudget scale'.size := by
    unfold boundedNatToBinaryWorkBudget
    gcongr
  have labelsFee : labelFee labels ≤ labelFee labels' := by
    unfold labelFee boundedNatToBinaryWorkBudget
    gcongr
  unfold binaryForestRoundAdditionalWorkBudget
  change (5*h+7*vertices+13)+(2+free*(2*labelFee labels+6))+(7*scale+3)+boundedNatToBinaryWorkBudget scale.size+
      forestUnitTrialRowsWordBudget h scale trials links W (U keys free labels cost amount scale)+11 ≤
    (5*h+7*vertices'+13)+(2+free'*(2*labelFee labels'+6))+(7*scale'+3)+boundedNatToBinaryWorkBudget scale'.size+
      forestUnitTrialRowsWordBudget h scale' trials' links' W (U keys' free' labels' cost' amount' scale')+11
  gcongr

/-- Bound the metered early metric by the number of original vertices,
height, seed-reader fee and demand count. -/
def finSteinerBinaryEarlyMetricSizeBudget (n h seedFee p : ℕ) : ℕ :=
  let forest := 2*n*(n+1)^h
  let depth := 6*n*(n+1)^h
  let keys := depth^2
  let scale := 1+n*forest^2
  let fuel := (scale+1)*scale+1
  let trials := 16*(h+1)^2*(n+1)
  let readFee := n^2
  let labelFee := heightNodeIndexWordBudget h 1+boundedNatToBinaryWorkBudget depth+23
  let amount := n+(p*fuel)*(1+p*fuel+1)
  (finForestNetworkPairKeysWordPolynomial n h+3)+(5*h+7*depth+13)+(7*n+3)+
    forestWeightedRequestsWorkBudget h forest keys keys p+
    binaryWeightedNetworkFromZeroWorkBudget depth keys keys keys depth n (12*keys+10*h+8*readFee+53)
      labelFee scale fuel p+11+
    binaryForestRoundAdditionalWorkBudget h depth keys keys depth n amount scale trials (forest^2) readFee+
    trials*(forest^2*((scale+1)*((h+2)*seedFee)))+5

set_option maxHeartbeats 1400000 in
/-- The graph-specific early work allowance is bounded entirely by the
input sizes, including all typed forest counts and the weighted fuel. -/
theorem finSteinerBinaryEarlyMetricWorkBudget_le_size {n : ℕ} (G : Arcs (Fin n)) (h seedFee p : ℕ) :
    finSteinerBinaryEarlyMetricWorkBudget G h seedFee p ≤ finSteinerBinaryEarlyMetricSizeBudget n h seedFee p := by
  let forest := 2*n*(n+1)^h
  let depth := 6*n*(n+1)^h
  let keys := depth^2
  let S := 1+n*forest^2
  let F := (S+1)*S+1
  let T := 16*(h+1)^2*(n+1)
  let rows := finForestNetworkRowsWithWordWork n h
  let index := binaryFinForestNetworkLabelsWithWork n h
  let paid := forestNetworkPriced G (heightForest G h)
  let free := forestNetworkZero G h
  let weight := forestNetworkWeight G (height := h)
  let scale := forestScale G h
  let fuel := weightedCoverFuel paid weight
  let trials := earlyTrialCount (Fin n) h
  let links := (heightForest G h).card
  obtain ⟨_,_,forestRows,_,_,keyCount,_⟩ := finForestNetworkRowsWithWordWork_spec n h
  obtain ⟨exactDepth,depthCount,exactWidth,_,_,_⟩ := binaryFinForestNetworkLabelsWithWork_spec n h
  have fullForest : rows.vertices.toFinset = univ := by
    ext v
    simp only [List.mem_toFinset,Finset.mem_univ,iff_true]
    exact (finForestNetworkRowsWithWordWork_spec n h).2.1 v
  have forestEq : Fintype.card (HeightForestVertex (Fin n) h) = rows.vertices.length := by
    rw [← Finset.card_univ,← fullForest,List.toFinset_card_of_nodup (finForestNetworkRowsWithWordWork_spec n h).1]
  have linksCap : links ≤ forest^2 := by
    refine (card_le_univ _).trans ?_
    rw [Fintype.card_prod,← pow_two,forestEq]
    exact Nat.pow_le_pow_left forestRows 2
  have arcsCap (E : Arcs (ForestNetworkVertex (Fin n) h)) : E.card ≤ keys := by
    refine (card_le_univ E).trans ?_
    rw [Fintype.card_prod,← pow_two,← exactDepth]
    exact Nat.pow_le_pow_left depthCount 2
  have labels : index.width ≤ depth := by
    rw [show index.width = index.count.size from exactWidth]
    exact (Nat.size_le.mpr index.count.lt_two_pow_self).trans depthCount
  have cost : n.size ≤ n := Nat.size_le.mpr n.lt_two_pow_self
  have scaleBound : scale ≤ S := by
    change weightedCoverScale paid weight ≤ S
    refine (forestNetworkScale_le G h).trans ?_
    rw [Fintype.card_fin,forestEq]
    exact max_le (Nat.le_add_right 1 _) ((Nat.mul_le_mul_left n (Nat.pow_le_pow_left forestRows 2)).trans
      (Nat.le_add_left _ 1))
  have totalBound : (∑ e ∈ paid, weight e) ≤ S := (le_max_right 1 _).trans scaleBound
  have logBound : scale.log2 ≤ S := (Nat.log2_le_self _).trans scaleBound
  have fuelBound : fuel ≤ F := by
    dsimp only [fuel,weightedCoverFuel,F]
    exact Nat.add_le_add_right (Nat.mul_le_mul (Nat.add_le_add_right logBound 1) totalBound) 1
  have trialsCap : trials ≤ T := by
    simp only [trials,T,earlyTrialCount,Fintype.card_fin]
    gcongr
    exact Nat.log2_le_self n
  have templateCharge : 5*h+7*index.count+13 ≤ 5*h+7*depth+13 := by gcongr
  have requestCharge : forestWeightedRequestsWorkBudget h rows.vertices.length rows.keys.length free.card p ≤
      forestWeightedRequestsWorkBudget h forest keys keys p := by
    have prep := forestRequestWordBudget_le (height := h) forestRows (arcsCap free)
    unfold forestWeightedRequestsWorkBudget
    gcongr
  have paidCap := arcsCap paid
  have costRead : 12*paid.card+10*h+8*n^2+53 ≤ 12*keys+10*h+8*n^2+53 := by gcongr
  have labelRead : heightNodeIndexWordBudget h 1+boundedNatToBinaryWorkBudget index.width+23 ≤
      heightNodeIndexWordBudget h 1+boundedNatToBinaryWorkBudget depth+23 := by
    unfold boundedNatToBinaryWorkBudget
    gcongr
  have solve := binaryWeightedNetworkFromZeroWorkBudget_le_dimensions p depthCount (arcsCap paid) keyCount
    keyCount labels cost costRead labelRead scaleBound fuelBound
  have amount : n.size+(p*fuel)*(1+p*fuel+1) ≤ n+(p*F)*(1+p*F+1) := by gcongr
  have rounding := binaryForestRoundAdditionalWorkBudget_le_dimensions (h := h) depthCount keyCount (arcsCap free)
    labels cost amount scaleBound trialsCap linksCap (readFee := n^2)
  have sampleFee : trials*(links*((scale.log2+1)*((h+2)*seedFee))) ≤
      T*(forest^2*((S+1)*((h+2)*seedFee))) := by gcongr
  unfold finSteinerBinaryEarlyMetricWorkBudget binaryEarlyMetricWorkBudgetForLength
    binaryForestFractionalWorkBudgetForLength finSteinerBinaryEarlyMetricSizeBudget
  dsimp only
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_right (Nat.add_le_add
    (Nat.add_le_add (Nat.add_le_add_right (Nat.add_le_add_left templateCharge _) _) requestCharge) solve) 11)
    rounding) sampleFee) 5

end OnlineReachabilityPreservers
