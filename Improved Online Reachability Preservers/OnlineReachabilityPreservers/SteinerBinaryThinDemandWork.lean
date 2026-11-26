import OnlineReachabilityPreservers.SteinerBinaryThinLoopWork
import OnlineReachabilityPreservers.SteinerThinBitServiceWork

/-! Round one updated thin prefix and keep both the rounded arcs and its service decision. -/

namespace OnlineReachabilityPreservers

/-- Keep the ordered rounded arc labels and decide the miss flag on those
same rows. Only one threshold scan runs. -/
def binaryThinRoundedTrialWithWork {n : ℕ} (base factor : List Bool) (cells : List (List Bool))
    (rows : List (BinaryThinThresholdRow n)) (source target : List Bool) (depth : ℕ) :
    (List (List Bool × List Bool) × Bool) × ℕ :=
  let passed := roundBinaryThinEncodedRowsWithWork base factor cells rows
  let tested := binaryReachTestListWithWork passed.1 source target depth
  ((passed.1,!tested.1),passed.2+tested.2+7)

/-- Keep the exact reference rounded arc set and miss flag while reusing the
actual binary label scan. -/
theorem binaryThinRoundedTrialWithWork_refines {n labels sampleWidth width : ℕ}
    (table : FinThinLoadTable n) (base factor : List Bool) (cells : List (List Bool))
    (rows : List (BinaryThinThresholdRow n)) (encoded : EncodesThinLoadTable table cells width)
    (size : binaryWordValue base = n)
    (bounds : ∀ row ∈ rows, BinaryThinArcMatches labels row.labels row.arc ∧ row.sample.length ≤ sampleWidth)
    (code : Fin n → List Bool) (injective : Function.Injective code) (bounded : ∀ v, (code v).length ≤ labels)
    (matchLabels : ∀ row ∈ rows, row.labels = (code row.arc.1,code row.arc.2))
    (unique : ((rows.map BinaryThinThresholdRow.reference).map Prod.fst).Nodup) (demand : Fin n × Fin n) :
    let out := binaryThinRoundedTrialWithWork base factor cells rows (code demand.1) (code demand.2) n
    let ref := roundThinServiceWithWordWork (rows.map BinaryThinThresholdRow.reference) unique
      (binaryWordValue factor) (fun arc => (table.read arc,0)) n demand
    (∃ kept : List (Fin n × Fin n), out.1.1 = binaryEncodeArcs code kept ∧ kept.toFinset = ref.1.1) ∧
      out.1.2 = ref.1.2.1 ∧
      out.2 ≤ binaryThinServiceWorkBudget n rows.length base.length labels sampleWidth factor.length width n+2 := by
  let passed := roundBinaryThinEncodedRowsWithWork base factor cells rows
  let kept := roundBinaryThinThresholdRowsWithWork base factor cells rows
  let tested := binaryReachTestListWithWork passed.1 (code demand.1) (code demand.2) n
  let ref := roundThinServiceWithWordWork (rows.map BinaryThinThresholdRow.reference) unique
    (binaryWordValue factor) (fun arc => (table.read arc,0)) n demand
  obtain ⟨encodedRows,_⟩ := roundBinaryThinEncodedRowsWithWork_spec table base factor cells rows encoded size bounds
  obtain ⟨typedRows,_⟩ := roundBinaryThinThresholdRowsWithWork_spec table base factor cells rows encoded size bounds
  obtain ⟨set,_⟩ := roundBinaryThinThresholdRowsWithWork_refines table base factor cells rows encoded size bounds unique
  obtain ⟨refResult,_⟩ := roundThinServiceWithWordWork_spec (rows.map BinaryThinThresholdRow.reference) unique
    (binaryWordValue factor) (fun arc => (table.read arc,0)) n (by simp) demand
  obtain ⟨miss,cost⟩ := roundBinaryThinServiceWithWork_refines table base factor cells rows encoded size bounds code
    injective bounded matchLabels unique demand
  have sameRows : passed.1 = binaryEncodeArcs code kept.1 := by
    change passed.1 = _ at encodedRows
    change kept.1 = _ at typedRows
    rw [encodedRows,typedRows,binaryEncodeArcs,List.map_map]
    apply List.map_congr_left
    intro row present
    exact matchLabels row (List.mem_filter.mp present).1
  have graph : kept.1.toFinset = ref.1.1 :=
    set.trans (congrArg Prod.fst refResult).symm
  refine ⟨⟨kept.1,sameRows,graph⟩,miss,?_⟩
  change passed.2+tested.2+5 ≤ _ at cost
  change passed.2+tested.2+7 ≤ _
  omega

/-- Store the updated table, the cut count, and the result of its rounding. -/
structure BinaryThinDemandResult where
  cells : List (List Bool)
  updates : ℕ
  rounded : List (List Bool × List Bool)
  missed : Bool

/-- Finish the fractional loop for the arriving demand before rounding
its updated loads. The threshold rows are supplied. -/
def binaryThinDemandWithWork {n : ℕ} (arcs keys : List (List Bool × List Bool))
    (base ceiling factor : List Bool) (cells : List (List Bool)) (rows : List (BinaryThinThresholdRow n))
    (source target : List Bool) (depth supply fuel : ℕ) : BinaryThinDemandResult × ℕ :=
  let loads := binaryThinLoopWithWork arcs keys base ceiling source target depth supply fuel cells
  let trial := binaryThinRoundedTrialWithWork base factor loads.1.1 rows source target depth
  (⟨loads.1.1,loads.1.2,trial.1.1,trial.1.2⟩,loads.2+trial.2+6)

/-- The per-demand binary step reproduces the reference loads, count,
rounded arc set and miss flag when given the corresponding threshold rows. -/
theorem binaryThinDemandWithWork_refines {n labels sampleWidth width : ℕ}
    (arcs keys : List (Fin n × Fin n)) (demand : Fin n × Fin n) (reachable : Reach arcs.toFinset demand.1 demand.2)
    (simple : arcs.Nodup) (complete : ∀ e, e ∈ keys)
    (code : Fin n → List Bool) (numeric : ∀ v, binaryWordValue (code v) = v.val)
    (bounded : ∀ v, (code v).length ≤ labels) (base ceiling factor : List Bool)
    (size : binaryWordValue base = n) (supply : binaryWordValue ceiling = arcs.toFinset.card)
    (widthFits : arcs.toFinset.card.log2+1 < 2^width)
    (table : FinThinLoadTable n) (cells : List (List Bool))
    (encoded : EncodesThinLoadTable table cells width)
    (invariant : ∀ e ∈ arcs.toFinset, table.read e ≤ arcs.toFinset.card.log2+1)
    (rows : List (BinaryThinThresholdRow n))
    (bounds : ∀ row ∈ rows, BinaryThinArcMatches labels row.labels row.arc ∧ row.sample.length ≤ sampleWidth)
    (matchLabels : ∀ row ∈ rows, row.labels = (code row.arc.1,code row.arc.2))
    (unique : ((rows.map BinaryThinThresholdRow.reference).map Prod.fst).Nodup) :
    let G := arcs.toFinset
    let fuel := G.card*(G.card.log2+1)+1
    let active := arcs.filter fun e => decide (e ∈ intervalArcs G demand)
    let out := binaryThinDemandWithWork (binaryEncodeArcs code arcs) (binaryEncodeArcs code keys)
      base ceiling factor cells rows (code demand.1) (code demand.2) n G.card fuel
    let current := thinCoverLoop G demand fuel table.read
    let ref := roundThinServiceWithWordWork (rows.map BinaryThinThresholdRow.reference) unique
      (binaryWordValue factor) (fun e => (current.1 e,0)) n demand
    (∃ finishing : FinThinLoadTable n, EncodesThinLoadTable finishing out.1.cells width ∧ finishing.read = current.1 ∧
      (∀ e ∈ G, finishing.read e ≤ G.card.log2+1)) ∧ out.1.updates = current.2 ∧
      (∃ kept : List (Fin n × Fin n), out.1.rounded = binaryEncodeArcs code kept ∧ kept.toFinset = ref.1.1) ∧
      out.1.missed = ref.1.2.1 ∧
      out.2 ≤ binaryDemandIntervalArcsWorkBudget n arcs.length labels n+
        (out.1.updates+1)*binaryPreparedThinLoopStepWorkBudget n active.length keys.length
          base.length labels width ceiling.length G.card+
        binaryThinServiceWorkBudget n rows.length base.length labels sampleWidth factor.length width n+14 := by
  have injective : Function.Injective code := fun a b equal =>
    Fin.ext ((numeric a).symm.trans ((congrArg binaryWordValue equal).trans (numeric b)))
  let G := arcs.toFinset
  let fuel := G.card*(G.card.log2+1)+1
  let loads := binaryThinLoopWithWork (binaryEncodeArcs code arcs) (binaryEncodeArcs code keys)
    base ceiling (code demand.1) (code demand.2) n G.card fuel cells
  let trial := binaryThinRoundedTrialWithWork base factor loads.1.1 rows (code demand.1) (code demand.2) n
  obtain ⟨ending,represented,exactLoads,count,keptInvariant,loadCost⟩ := binaryThinLoopWithWork_refines arcs keys demand
    reachable simple complete code numeric bounded base ceiling size supply widthFits fuel table cells encoded invariant
  change EncodesThinLoadTable ending loads.1.1 width at represented
  obtain ⟨exactRounded,miss,roundCost⟩ := binaryThinRoundedTrialWithWork_refines ending base factor loads.1.1 rows
    represented size bounds code injective bounded matchLabels unique demand
  change ending.read = (thinCoverLoop G demand fuel table.read).1 at exactLoads
  rw [exactLoads] at exactRounded miss
  refine ⟨⟨ending,represented,exactLoads,keptInvariant⟩,count,exactRounded,miss,?_⟩
  let active := arcs.filter fun e => decide (e ∈ intervalArcs G demand)
  let fee := binaryDemandIntervalArcsWorkBudget n arcs.length labels n+
    (loads.1.2+1)*binaryPreparedThinLoopStepWorkBudget n active.length keys.length base.length labels width ceiling.length G.card
  let rounding := binaryThinServiceWorkBudget n rows.length base.length labels sampleWidth factor.length width n
  change loads.2 ≤ fee+6 at loadCost
  change trial.2 ≤ rounding+2 at roundCost
  change loads.2+trial.2+6 ≤ fee+rounding+14
  omega

end OnlineReachabilityPreservers
