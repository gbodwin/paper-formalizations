import OnlineReachabilityPreservers.SteinerBinaryWeightedUpdateWork

/-! Generate weighted cuts and advance the same binary state across a demand. -/

namespace OnlineReachabilityPreservers

/-- Run a request-local weighted cover. The result keeps the final pair
table and the chosen paid cuts in chronological order. -/
def binaryWeightedCoverLoopWithWork {V : Type*} (arcs free : List (List Bool × List Bool))
    (ceiling source target : List Bool) (depth supply : ℕ) : ℕ → List (BinaryWeightedPairRow V) →
    (List (BinaryWeightedPairRow V) × List (List (List Bool × List Bool))) × ℕ
  | 0, rows => ((rows,[]),2)
  | fuel+1, rows =>
    let tested := binaryWeightedViolationWithWork arcs free ceiling rows source target depth supply
    match tested.1 with
    | none => ((rows,[]),tested.2+3)
    | some cut =>
      let advanced := chargeBinaryWeightedPairRowsWithWork cut rows
      let tail := binaryWeightedCoverLoopWithWork arcs free ceiling source target depth supply fuel advanced.1
      ((tail.1.1,cut::tail.1.2),tested.2+advanced.2+tail.2+8)

private def binaryWeightedCoverStepBudget (n arcs rows free labels cost remainder power amount cap supply : ℕ) : ℕ :=
  binaryWeightedCapacityRowsWorkBudget rows free labels cost amount supply+
    binaryLowCapacityOutgoingCutWorkBudget n arcs rows labels (max cap supply) supply+
    chargeBinaryWeightedPairRowsWorkBudget rows arcs labels cost remainder power amount+13

def binaryWeightedCoverLoopWorkBudget (n arcs rows free labels cost remainder power amount cap supply fuel : ℕ) : ℕ :=
  2+fuel*binaryWeightedCoverStepBudget n arcs rows free labels cost (remainder+fuel) (power+fuel)
    (amount+fuel*(power+fuel+1)) cap supply

private theorem binaryWeightedCoverStepBudget_mono (n arcs rows free labels cost cap supply : ℕ)
    {r r' p p' a a' : ℕ} (rem : r ≤ r') (pow : p ≤ p') (amt : a ≤ a') :
    binaryWeightedCoverStepBudget n arcs rows free labels cost r p a cap supply ≤
      binaryWeightedCoverStepBudget n arcs rows free labels cost r' p' a' cap supply := by
  have divCost := binaryCeilingDivWorkBudget_mono_widths amt (le_refl cost) 0 0 supply
  unfold binaryWeightedCoverStepBudget binaryWeightedCapacityRowsWorkBudget binaryWeightedCapacityAtWorkBudget
    chargeBinaryWeightedPairRowsWorkBudget chargeBinaryWeightedPairRowWorkBudget chargeBinaryWeightedLoadWorkBudget
  gcongr

theorem BinaryWeightedPairRow.amount_le {V : Type*} {edges : Arcs V} {weight charges : V × V → ℕ}
    {code : V → List Bool} {cost a a' : ℕ} {row : BinaryWeightedPairRow V}
    (stored : row.Encodes edges weight charges code cost a) (bound : a ≤ a') :
    row.Encodes edges weight charges code cost a' := by
  obtain ⟨labels,paid,unpaid⟩ := stored
  refine ⟨labels,?_,unpaid⟩
  intro inside
  obtain ⟨c,s,shape,value,encoded,short,amount⟩ := paid inside
  exact ⟨c,s,shape,value,encoded,short,amount.trans bound⟩

theorem BinaryWeightedPairRow.chargeWidths_le {V : Type*} {r r' p p' : ℕ} {row : BinaryWeightedPairRow V}
    (widths : row.ChargeWidths r p) (rem : r ≤ r') (pow : p ≤ p') : row.ChargeWidths r' p' := by
  intro cost state present
  obtain ⟨left,right⟩ := widths cost state present
  exact ⟨left.trans rem,right.trans pow⟩

variable {V : Type*} [LinearOrder V] [Fintype V]

set_option maxHeartbeats 900000 in
/-- The binary weighted loop returns the exact reference charges and
chronological paid cuts. The bound includes every separated cut, its table
update, and the final probe when one is reached. -/
theorem binaryWeightedCoverLoopWithWork_refines (arcs free : List (V × V)) (source target : V) (supply fuel : ℕ)
    (simple : arcs.Nodup) (weight charges : V × V → ℕ) (positive : ∀ e ∈ arcs.toFinset, 0 < weight e)
    (ceiling : List Bool) (supplyWord : binaryWordValue ceiling = supply) (code : V → List Bool)
    (injective : Function.Injective code) (labels costWidth remainderWidth powerWidth amountWidth : ℕ)
    (bounded : ∀ v, (code v).length ≤ labels) (rows : List (BinaryWeightedPairRow V))
    (complete : ∀ e, e ∈ rows.map BinaryWeightedPairRow.arc)
    (encoded : ∀ row ∈ rows, row.Encodes arcs.toFinset weight charges code costWidth amountWidth)
    (widths : ∀ row ∈ rows, row.ChargeWidths remainderWidth powerWidth) :
    let demand : WeightedNetworkDemand V := ⟨free.toFinset,source,target⟩
    let reference := weightedCoverLoop (weightedNetworkViolation arcs.toFinset demand weight supply) fuel charges
    let out := binaryWeightedCoverLoopWithWork (binaryEncodeArcs code arcs) (binaryEncodeArcs code free) ceiling (code source)
      (code target) (Fintype.card V) supply fuel rows
    out.1.1.map BinaryWeightedPairRow.arc = rows.map BinaryWeightedPairRow.arc ∧
    (∀ row ∈ out.1.1, row.Encodes arcs.toFinset weight reference.1 code costWidth (amountWidth+fuel*(powerWidth+fuel+1))) ∧
    (∀ row ∈ out.1.1, row.ChargeWidths (remainderWidth+fuel) (powerWidth+fuel)) ∧
    (∃ cuts : List (List (V × V)), out.1.2 = cuts.map (binaryEncodeArcs code) ∧ cuts.map List.toFinset = reference.2) ∧
    out.2 ≤ binaryWeightedCoverLoopWorkBudget (Fintype.card V) arcs.length rows.length free.length labels costWidth
      remainderWidth powerWidth amountWidth ceiling.length supply fuel := by
  let G := arcs.toFinset
  let demand : WeightedNetworkDemand V := ⟨free.toFinset,source,target⟩
  let search := weightedNetworkViolation G demand weight supply
  let depth := Fintype.card V
  let paidBits := binaryEncodeArcs code arcs
  let freeBits := binaryEncodeArcs code free
  change let reference := weightedCoverLoop search fuel charges
    let out := binaryWeightedCoverLoopWithWork paidBits freeBits ceiling (code source) (code target) depth supply fuel rows
    out.1.1.map BinaryWeightedPairRow.arc = rows.map BinaryWeightedPairRow.arc ∧
    (∀ row ∈ out.1.1, row.Encodes G weight reference.1 code costWidth (amountWidth+fuel*(powerWidth+fuel+1))) ∧
    (∀ row ∈ out.1.1, row.ChargeWidths (remainderWidth+fuel) (powerWidth+fuel)) ∧
    (∃ cuts : List (List (V × V)), out.1.2 = cuts.map (binaryEncodeArcs code) ∧ cuts.map List.toFinset = reference.2) ∧
    out.2 ≤ binaryWeightedCoverLoopWorkBudget depth arcs.length rows.length free.length labels costWidth
      remainderWidth powerWidth amountWidth ceiling.length supply fuel
  induction fuel generalizing rows charges remainderWidth powerWidth amountWidth with
  | zero =>
    simp only [binaryWeightedCoverLoopWithWork,weightedCoverLoop,Nat.zero_mul,Nat.add_zero,binaryWeightedCoverLoopWorkBudget]
    exact ⟨trivial,encoded,widths,⟨[],rfl,rfl⟩,le_rfl⟩
  | succ fuel ih =>
    let probe := binaryWeightedViolationWithWork paidBits freeBits ceiling rows (code source) (code target) depth supply
    let R := remainderWidth+(fuel+1)
    let P := powerWidth+(fuel+1)
    let A := amountWidth+(fuel+1)*(powerWidth+(fuel+1)+1)
    let fee := binaryWeightedCoverStepBudget depth arcs.length rows.length free.length labels costWidth R P A ceiling.length supply
    obtain ⟨exactCut,probeCost⟩ := binaryWeightedViolationWithWork_refines arcs free source target supply weight charges positive
      ceiling supplyWord code injective labels costWidth amountWidth bounded rows complete encoded
    have loR : remainderWidth ≤ R := Nat.le_add_right _ _
    have loP : powerWidth ≤ P := Nat.le_add_right _ _
    have loA : amountWidth ≤ A := Nat.le_add_right _ _
    have pollBound : probe.2 ≤ binaryWeightedCapacityRowsWorkBudget rows.length free.length labels costWidth A supply+
        binaryLowCapacityOutgoingCutWorkBudget depth arcs.length rows.length labels (max ceiling.length supply) supply+5 := by
      have amounts := binaryCeilingDivWorkBudget_mono_widths loA (le_refl costWidth) 0 0 supply
      apply probeCost.trans
      unfold binaryWeightedCapacityRowsWorkBudget binaryWeightedCapacityAtWorkBudget
      gcongr
    change (match search charges with
      | none => probe.1 = none
      | some C => ∃ cut : List (V × V), probe.1 = some (binaryEncodeArcs code cut) ∧
        cut.toFinset = C ∧ (arcs.Nodup → cut.Nodup)) at exactCut
    cases found : search charges with
    | none =>
      rw [found] at exactCut
      change probe.1 = none at exactCut
      dsimp only
      rw [binaryWeightedCoverLoopWithWork,weightedCoverLoop,found,exactCut]
      refine ⟨rfl,fun row present => BinaryWeightedPairRow.amount_le (encoded row present) loA,
        fun row present => BinaryWeightedPairRow.chargeWidths_le (widths row present) loR loP,⟨[],rfl,rfl⟩,?_⟩
      change probe.2+3 ≤ 2+(fuel+1)*fee
      rw [Nat.add_mul,Nat.one_mul]
      unfold fee binaryWeightedCoverStepBudget
      omega
    | some C =>
      rw [found] at exactCut
      obtain ⟨cut,observed,cutSet,distinct⟩ := exactCut
      let next := chargeBinaryWeightedPairRowsWithWork (binaryEncodeArcs code cut) rows
      let nextCharges := chargeWeightedCut C charges
      obtain ⟨keys,_,encodedNext,widthsNext,advanceCost⟩ := chargeBinaryWeightedPairRowsWithWork_spec G weight charges positive
        cut code injective labels costWidth remainderWidth powerWidth amountWidth bounded rows encoded widths
      change next.1.map BinaryWeightedPairRow.arc = rows.map BinaryWeightedPairRow.arc at keys
      have allNext : ∀ e, e ∈ next.1.map BinaryWeightedPairRow.arc := by intro e; rw [keys]; exact complete e
      have nextCount : next.1.length = rows.length := by
        simpa only [List.length_map] using congrArg List.length keys
      rw [cutSet] at encodedNext
      obtain ⟨ending,table,remaining,⟨cuts,observedCuts,actualCuts⟩,lastCost⟩ :=
        ih nextCharges (remainderWidth+1) (powerWidth+1) (amountWidth+powerWidth+1) next.1 allNext encodedNext widthsNext
      let tail := binaryWeightedCoverLoopWithWork paidBits freeBits ceiling (code source) (code target) depth supply fuel next.1
      have enoughA : amountWidth+powerWidth+1+fuel*(powerWidth+1+fuel+1) ≤ A := by
        dsimp only [A]
        rw [Nat.add_mul,Nat.one_mul]
        rw [show powerWidth+1+fuel+1 = powerWidth+(fuel+1)+1 by omega]
        omega
      have remEq : remainderWidth+1+fuel = R := by dsimp only [R]; omega
      have powEq : powerWidth+1+fuel = P := by dsimp only [P]; omega
      let nextA := amountWidth+powerWidth+1+fuel*(P+1)
      have nextAmountFits : nextA ≤ A := by
        change amountWidth+powerWidth+1+fuel*(P+1) ≤ A
        rw [← powEq]
        exact enoughA
      let nextFee := binaryWeightedCoverStepBudget depth arcs.length rows.length free.length labels costWidth R P nextA
        ceiling.length supply
      have tailFits : tail.2 ≤ 2+fuel*fee := by
        change tail.2 ≤ _ at lastCost
        unfold binaryWeightedCoverLoopWorkBudget at lastCost
        rw [nextCount,remEq,powEq] at lastCost
        change tail.2 ≤ 2+fuel*nextFee at lastCost
        have feeFits : nextFee ≤ fee :=
          binaryWeightedCoverStepBudget_mono depth arcs.length rows.length free.length labels costWidth ceiling.length supply
            (r := R) (r' := R) (p := P) (p' := P) (a := nextA) (a' := A) le_rfl le_rfl nextAmountFits
        exact lastCost.trans (Nat.add_le_add_left (Nat.mul_le_mul_left fuel feeFits) 2)
      obtain ⟨_,side,_,_,_,outgoing⟩ := weightedNetworkViolation_some (edges := G) (d := demand)
        (weight := weight) (charges := charges) (scale := supply) positive found
      have sub : cut.toFinset ⊆ G := by
        rw [cutSet,outgoing]
        exact Finset.filter_subset _ _
      have size : cut.length ≤ arcs.length := by
        rw [← List.toFinset_card_of_nodup (distinct simple),← List.toFinset_card_of_nodup simple]
        exact Finset.card_le_card sub
      have updateFits : next.2 ≤ chargeBinaryWeightedPairRowsWorkBudget rows.length arcs.length labels costWidth R P A := by
        apply advanceCost.trans
        unfold chargeBinaryWeightedPairRowsWorkBudget chargeBinaryWeightedPairRowWorkBudget chargeBinaryWeightedLoadWorkBudget
        gcongr
      dsimp only
      rw [binaryWeightedCoverLoopWithWork,weightedCoverLoop,found,observed]
      refine ⟨ending.trans keys,?_,?_,⟨cut::cuts,?_,?_⟩,?_⟩
      · intro row present
        exact BinaryWeightedPairRow.amount_le (table row present) enoughA
      · intro row present
        exact BinaryWeightedPairRow.chargeWidths_le (remaining row present) (le_of_eq remEq) (le_of_eq powEq)
      · change binaryEncodeArcs code cut::tail.1.2 = _
        rw [show tail.1.2 = cuts.map (binaryEncodeArcs code) from observedCuts]
        rfl
      · simpa only [List.map_cons,cutSet] using congrArg (C::·) actualCuts
      · have stepCost : probe.2+next.2+8 ≤ fee := by
          unfold fee binaryWeightedCoverStepBudget
          omega
        change probe.2+next.2+tail.2+8 ≤ 2+(fuel+1)*fee
        rw [Nat.add_mul,Nat.one_mul]
        omega

/-- Increasing the free-list size or any of the starting state widths
increases the uniform allowance for the same fixed fuel. -/
theorem binaryWeightedCoverLoopWorkBudget_le (n arcs rows labels cost cap supply fuel : ℕ)
    {free free' r r' p p' a a' : ℕ} (freeSize : free ≤ free') (rem : r ≤ r') (pow : p ≤ p') (amt : a ≤ a') :
    binaryWeightedCoverLoopWorkBudget n arcs rows free labels cost r p a cap supply fuel ≤
      binaryWeightedCoverLoopWorkBudget n arcs rows free' labels cost r' p' a' cap supply fuel := by
  have amount : a+fuel*(p+fuel+1) ≤ a'+fuel*(p'+fuel+1) := by gcongr
  have divCost := binaryCeilingDivWorkBudget_mono_widths amount (le_refl cost) 0 0 supply
  unfold binaryWeightedCoverLoopWorkBudget binaryWeightedCoverStepBudget binaryWeightedCapacityRowsWorkBudget
    binaryWeightedCapacityAtWorkBudget chargeBinaryWeightedPairRowsWorkBudget chargeBinaryWeightedPairRowWorkBudget
    chargeBinaryWeightedLoadWorkBudget
  gcongr

end OnlineReachabilityPreservers
