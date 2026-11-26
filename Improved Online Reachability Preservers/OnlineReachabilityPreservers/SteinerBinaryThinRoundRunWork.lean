import OnlineReachabilityPreservers.SteinerBinaryThinCoverWork
import OnlineReachabilityPreservers.SteinerBinaryThinDemandWork

/-! Carry out fractional updates and rounded service tests in chronological order. -/

namespace OnlineReachabilityPreservers

open Finset

/-- The last load table and rounded graph, with total updates and a sticky miss flag. -/
structure BinaryThinRoundRunState where
  cells : List (List Bool)
  rounded : List (List Bool × List Bool)
  updates : ℕ
  missed : Bool

/-- Carry the actual binary table from one demand to the next. Keep the
latest rounded arc list and combine the per-demand miss flags. -/
def binaryThinRoundRunFromWithWork {n : ℕ} (arcs keys : List (List Bool × List Bool))
    (base ceiling factor : List Bool) (rows : List (BinaryThinThresholdRow n)) (depth supply fuel : ℕ) :
    List (List Bool × List Bool) → List (List Bool) → List (List Bool × List Bool) → BinaryThinRoundRunState × ℕ
  | [], cells, prior => (⟨cells,prior,0,false⟩,2)
  | demand::rest, cells, _ =>
    let first := binaryThinDemandWithWork arcs keys base ceiling factor cells rows demand.1 demand.2 depth supply fuel
    let tail := binaryThinRoundRunFromWithWork arcs keys base ceiling factor rows depth supply fuel rest
      first.1.cells first.1.rounded
    (⟨tail.1.cells,tail.1.rounded,first.1.updates+tail.1.updates,first.1.missed || tail.1.missed⟩,
      first.2+tail.2+8)

/-- The reference miss tests use the updated fractional loads of each arrival. -/
def thinRoundRunMissFrom {n : ℕ} (G : Arcs (Fin n)) (round : CutLoads (Fin n) → Arcs (Fin n)) :
    List (Fin n × Fin n) → CutLoads (Fin n) → Bool
  | [], _ => false
  | demand::rest, load =>
    let next := thinCoverStep G demand load
    decide (demand.1 ∉ reaches (round next) demand.2) || thinRoundRunMissFrom G round rest next

/-- A uniform per-arrival allowance and the cost of the successful cuts. -/
def binaryThinRoundRunWorkBudget
    (n arcs keys rows base labels samples width ceiling factor supply demands updates : ℕ) : ℕ :=
  (demands+updates)*binaryPreparedThinLoopStepWorkBudget n arcs keys base labels width ceiling supply+
    demands*(binaryDemandIntervalArcsWorkBudget n arcs labels n+
      binaryThinServiceWorkBudget n rows base labels samples factor width n+22)+2

/-- The rounded binary run reproduces all fractional loads and the sticky
reference miss outcome, with the final rounded graph on every nonempty trace. -/
theorem binaryThinRoundRunFromWithWork_refines {n labels sampleWidth width : ℕ}
    (arcs keys demands prior : List (Fin n × Fin n)) (simple : arcs.Nodup) (complete : ∀ e, e ∈ keys)
    (reachable : ∀ demand ∈ demands, Reach arcs.toFinset demand.1 demand.2)
    (code : Fin n → List Bool) (numeric : ∀ v, binaryWordValue (code v) = v.val)
    (bounded : ∀ v, (code v).length ≤ labels) (base ceiling factor : List Bool)
    (size : binaryWordValue base = n) (supply : binaryWordValue ceiling = arcs.toFinset.card)
    (widthFits : arcs.toFinset.card.log2+1 < 2^width)
    (rows : List (BinaryThinThresholdRow n))
    (bounds : ∀ row ∈ rows, BinaryThinArcMatches labels row.labels row.arc ∧ row.sample.length ≤ sampleWidth)
    (matchLabels : ∀ row ∈ rows, row.labels = (code row.arc.1,code row.arc.2))
    (unique : ((rows.map BinaryThinThresholdRow.reference).map Prod.fst).Nodup)
    (table : FinThinLoadTable n) (cells : List (List Bool))
    (encoded : EncodesThinLoadTable table cells width)
    (invariant : ∀ e ∈ arcs.toFinset, table.read e ≤ arcs.toFinset.card.log2+1) :
    let G := arcs.toFinset
    let fuel := G.card*(G.card.log2+1)+1
    let round := roundedFromThinThresholdRows (rows.map BinaryThinThresholdRow.reference).toFinset (binaryWordValue factor)
    let out := binaryThinRoundRunFromWithWork (binaryEncodeArcs code arcs) (binaryEncodeArcs code keys)
      base ceiling factor rows n G.card fuel (binaryEncodeArcs code demands) cells (binaryEncodeArcs code prior)
    ∃ ending : FinThinLoadTable n, EncodesThinLoadTable ending out.1.cells width ∧
      ending.read = demands.foldl (fun load demand => thinCoverStep G demand load) table.read ∧
      (∀ e ∈ G, ending.read e ≤ G.card.log2+1) ∧
      (∃ selected : List (Fin n × Fin n), out.1.rounded = binaryEncodeArcs code selected ∧
        selected.toFinset = if demands.isEmpty then prior.toFinset else round ending.read) ∧
      out.1.missed = thinRoundRunMissFrom G round demands table.read ∧
      loadTotal G table.read+out.1.updates ≤ loadTotal G ending.read ∧
      out.2 ≤ binaryThinRoundRunWorkBudget n arcs.length keys.length rows.length base.length labels sampleWidth width
        ceiling.length factor.length G.card demands.length out.1.updates := by
  let G := arcs.toFinset
  let fuel := G.card*(G.card.log2+1)+1
  let arcBits := binaryEncodeArcs code arcs
  let keyBits := binaryEncodeArcs code keys
  let round := roundedFromThinThresholdRows (rows.map BinaryThinThresholdRow.reference).toFinset (binaryWordValue factor)
  let step := binaryPreparedThinLoopStepWorkBudget n arcs.length keys.length base.length labels width ceiling.length G.card
  let intervalCost := binaryDemandIntervalArcsWorkBudget n arcs.length labels n
  let roundCost := binaryThinServiceWorkBudget n rows.length base.length labels sampleWidth factor.length width n
  induction demands generalizing prior table cells with
  | nil =>
    refine ⟨table,encoded,rfl,invariant,⟨prior,rfl,rfl⟩,rfl,?_,?_⟩
    · simp [binaryThinRoundRunFromWithWork,binaryEncodeArcs]
    · simp [binaryThinRoundRunFromWithWork,binaryEncodeArcs,binaryThinRoundRunWorkBudget]
  | cons demand rest ih =>
    let first := binaryThinDemandWithWork arcBits keyBits base ceiling factor cells rows (code demand.1) (code demand.2)
      n G.card fuel
    let load := thinCoverLoop G demand fuel table.read
    let active := arcs.filter fun e => decide (e ∈ intervalArcs G demand)
    let activeStep := binaryPreparedThinLoopStepWorkBudget n active.length keys.length base.length labels width
      ceiling.length G.card
    let reference := roundThinServiceWithWordWork (rows.map BinaryThinThresholdRow.reference) unique
      (binaryWordValue factor) (fun e => (load.1 e,0)) n demand
    have request := reachable demand List.mem_cons_self
    obtain ⟨⟨next,nextEncoded,nextLoads,nextInvariant⟩,count,⟨selected,selectedBits,selectedSet⟩,miss,firstCost⟩ :=
      binaryThinDemandWithWork_refines arcs keys demand request simple complete code numeric bounded base ceiling factor
        size supply widthFits table cells encoded invariant rows bounds matchLabels unique
    change EncodesThinLoadTable next first.1.cells width at nextEncoded
    change next.read = load.1 at nextLoads
    change first.1.updates = load.2 at count
    change first.1.rounded = _ at selectedBits
    change selected.toFinset = reference.1.1 at selectedSet
    change first.1.missed = reference.1.2.1 at miss
    change first.2 ≤ intervalCost+(first.1.updates+1)*activeStep+roundCost+14 at firstCost
    have activeFits : activeStep ≤ step :=
      binaryPreparedThinLoopStepWorkBudget_le_arcs n keys.length base.length labels width ceiling.length G.card
        (List.length_filter_le _ _)
    have cost : first.2 ≤ intervalCost+(first.1.updates+1)*step+roundCost+14 := firstCost.trans (by gcongr)
    obtain ⟨refValue,_⟩ := roundThinServiceWithWordWork_spec (rows.map BinaryThinThresholdRow.reference) unique
      (binaryWordValue factor) (fun e => (load.1 e,0)) n (by simp) demand
    have kept : reference.1.1 = round load.1 := by
      have selectedRef := congrArg Prod.fst refValue
      change reference.1.1 = _ at selectedRef
      rw [selectedRef,roundThinThresholdListWithWordWork_spec]
    have missed : first.1.missed = decide (demand.1 ∉ reaches (round load.1) demand.2) := by
      rw [miss]
      have flag := congrArg (fun answer : Arcs (Fin n) × Bool × ℕ => answer.2.1) refValue
      change reference.1.2.1 = _ at flag
      rw [flag,reachInWithArcInspections_spec,roundThinThresholdListWithWordWork_spec]
      simp [reaches,round]
    have newLoad : next.read = thinCoverStep G demand table.read := nextLoads
    have progress : loadTotal G table.read+first.1.updates ≤ loadTotal G next.read := by
      rw [count,nextLoads]
      exact thinCoverLoop_load_progress G G Subset.rfl demand request fuel table.read invariant
    obtain ⟨ending,lastEncoded,lastLoad,lastInvariant,⟨keptRows,lastGraph,lastSet⟩,lastMiss,lastProgress,lastCost⟩ :=
      ih selected (fun d present => reachable d (List.mem_cons_of_mem _ present)) next first.1.cells nextEncoded nextInvariant
    rw [← selectedBits] at lastEncoded lastGraph lastMiss lastProgress lastCost
    let tail := binaryThinRoundRunFromWithWork arcBits keyBits base ceiling factor rows n G.card fuel
      (binaryEncodeArcs code rest) first.1.cells first.1.rounded
    change EncodesThinLoadTable ending tail.1.cells width at lastEncoded
    change tail.1.rounded = _ at lastGraph
    change tail.1.missed = thinRoundRunMissFrom G round rest next.read at lastMiss
    change loadTotal G next.read+tail.1.updates ≤ loadTotal G ending.read at lastProgress
    change tail.2 ≤ (rest.length+tail.1.updates)*step+rest.length*(intervalCost+roundCost+22)+2 at lastCost
    have latest : keptRows.toFinset = round ending.read := by
      rw [lastSet]
      cases rest with
      | nil =>
        simp only [List.isEmpty_nil,ite_true]
        change ending.read = next.read at lastLoad
        rw [lastLoad,nextLoads,selectedSet,kept]
      | cons head remaining => rfl
    rw [newLoad] at lastLoad lastMiss
    refine ⟨ending,lastEncoded,lastLoad,lastInvariant,⟨keptRows,lastGraph,latest⟩,?_,?_,?_⟩
    · change (first.1.missed || tail.1.missed) = _
      rw [missed,lastMiss]
      rfl
    · change loadTotal G table.read+(first.1.updates+tail.1.updates) ≤ loadTotal G ending.read
      omega
    · change first.2+tail.2+8 ≤ (rest.length+1+(first.1.updates+tail.1.updates))*step+
        (rest.length+1)*(intervalCost+roundCost+22)+2
      simp only [Nat.add_mul,Nat.one_mul] at cost lastCost ⊢
      omega

/-- The cumulative miss flag is true exactly when one chronological prefix
fails its own rounded demand test. -/
theorem thinRoundRunMissFrom_eq_true_iff {n : ℕ} (G : Arcs (Fin n))
    (round : CutLoads (Fin n) → Arcs (Fin n)) (demands : List (Fin n × Fin n)) (load : CutLoads (Fin n)) :
    thinRoundRunMissFrom G round demands load = true ↔
      ∃ i : Fin demands.length, (demands.get i).1 ∉ reaches
        (round ((demands.take (i.val+1)).foldl (fun current demand => thinCoverStep G demand current) load))
        (demands.get i).2 := by
  induction demands generalizing load with
  | nil => simp [thinRoundRunMissFrom]
  | cons demand rest ih =>
    simp only [thinRoundRunMissFrom,Bool.or_eq_true,decide_eq_true_eq,ih]
    constructor
    · rintro (first | ⟨i,present⟩)
      · exact ⟨0,by simpa using first⟩
      · exact ⟨i.succ,by simpa [List.take_succ_cons] using present⟩
    · rintro ⟨i,present⟩
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j,rfl⟩
      · exact Or.inl (by simpa using present)
      · exact Or.inr ⟨j,by simpa [List.take_succ_cons] using present⟩

/-- Start with zero loads. A miss at any prefix selects the original graph.
When every prefix succeeds, return the last rounded graph. -/
def binaryThinRoundRunWithWork {n : ℕ} (arcs keys : List (List Bool × List Bool))
    (base ceiling factor : List Bool) (rows : List (BinaryThinThresholdRow n)) (depth supply fuel : ℕ)
    (demands : List (List Bool × List Bool)) : List (List Bool × List Bool) × ℕ :=
  if demands.isEmpty then ([],2) else
    let width := reserveBinaryThinPayloadWithWork ceiling
    let start := emptyBinaryThinLoadsWithWork base width.1
    let run := binaryThinRoundRunFromWithWork arcs keys base ceiling factor rows depth supply fuel demands start.1 []
    (if run.1.missed then arcs else run.1.rounded,width.2+start.2+run.2+6)

/-- The top-level allowance uses the global load budget for the cut count. -/
def binaryThinRoundFromEmptyWorkBudget (n arcs keys rows base labels samples ceiling factor supply demands : ℕ) : ℕ :=
  reserveBinaryThinPayloadWorkBudget ceiling+emptyBinaryThinLoadWorkBudget n (ceiling+1) base (ceiling+1)+
    binaryThinRoundRunWorkBudget n arcs keys rows base labels samples (ceiling+1) ceiling factor supply
      demands (supply*(supply.log2+1))+6

/-- With the threshold rows for a fixed sample, the rounded binary run
implements the paper's exact thin graph, including the fallback. -/
theorem binaryThinRoundRunWithWork_refines {n labels sampleWidth : ℕ}
    (arcs keys demands : List (Fin n × Fin n)) (simple : arcs.Nodup) (complete : ∀ e, e ∈ keys)
    (reachable : ∀ demand ∈ demands, Reach arcs.toFinset demand.1 demand.2)
    (code : Fin n → List Bool) (numeric : ∀ v, binaryWordValue (code v) = v.val)
    (bounded : ∀ v, (code v).length ≤ labels) (base ceiling factor : List Bool)
    (size : binaryWordValue base = n) (supply : binaryWordValue ceiling = arcs.toFinset.card)
    (rows : List (BinaryThinThresholdRow n))
    (bounds : ∀ row ∈ rows, BinaryThinArcMatches labels row.labels row.arc ∧ row.sample.length ≤ sampleWidth)
    (matchLabels : ∀ row ∈ rows, row.labels = (code row.arc.1,code row.arc.2))
    (unique : ((rows.map BinaryThinThresholdRow.reference).map Prod.fst).Nodup) (sample : ThinSample arcs.toFinset)
    (thresholds : (rows.map BinaryThinThresholdRow.reference).toFinset =
      (prepareThinThresholdRowsWithSeedReads arcs.toFinset arcs.toFinset.card sample).1) :
    let G := arcs.toFinset
    let fuel := G.card*(G.card.log2+1)+1
    let out := binaryThinRoundRunWithWork (binaryEncodeArcs code arcs) (binaryEncodeArcs code keys)
      base ceiling factor rows n G.card fuel (binaryEncodeArcs code demands)
    (∃ selected : List (Fin n × Fin n), out.1 = binaryEncodeArcs code selected ∧
      selected.toFinset = thinRoundRun G (binaryWordValue factor) sample demands) ∧
    out.2 ≤ binaryThinRoundFromEmptyWorkBudget n arcs.length keys.length rows.length base.length labels sampleWidth
      ceiling.length factor.length G.card demands.length := by
  let G := arcs.toFinset
  let fuel := G.card*(G.card.log2+1)+1
  let arcBits := binaryEncodeArcs code arcs
  let keyBits := binaryEncodeArcs code keys
  let width := reserveBinaryThinPayloadWithWork ceiling
  let start := emptyBinaryThinLoadsWithWork base width.1
  let round := roundedFromThinThresholdRows (rows.map BinaryThinThresholdRow.reference).toFinset (binaryWordValue factor)
  let factorValue := binaryWordValue factor
  have sameRound : round = fun load => roundedThinArcs G factorValue load sample := by
    funext load
    change roundedFromThinThresholdRows (rows.map BinaryThinThresholdRow.reference).toFinset factorValue load = _
    rw [thresholds]
    exact (prepareThinThresholdRowsWithSeedReads_spec G G.card rfl sample).2 factorValue load
  have zero : (emptyFinThinLoads n).read = fun _ => 0 := by
    funext e
    simp [FinThinLoadTable.read,emptyFinThinLoads]
  cases demands with
  | nil =>
    refine ⟨⟨[],rfl,?_⟩,?_⟩
    · simp [thinRoundRun]
    · simp [binaryThinRoundRunWithWork,binaryEncodeArcs,binaryThinRoundFromEmptyWorkBudget]
  | cons demand rest =>
    let demands := demand::rest
    let demandBits := binaryEncodeArcs code demands
    let run := binaryThinRoundRunFromWithWork arcBits keyBits base ceiling factor rows n G.card fuel demandBits start.1 []
    obtain ⟨decoded,short,widthCost⟩ := reserveBinaryThinPayloadWithWork_spec ceiling
    change binaryWordValue width.1 = ceiling.length+1 at decoded
    change width.1.length ≤ ceiling.length+1 at short
    change width.2 ≤ _ at widthCost
    obtain ⟨encoded,startCost⟩ := emptyBinaryThinLoadsWithWork_spec base width.1 size
    change EncodesThinLoadTable (emptyFinThinLoads n) start.1 (binaryWordValue width.1) at encoded
    change start.2 ≤ _ at startCost
    rw [decoded] at encoded startCost
    have widthFits : G.card.log2+1 < 2^(ceiling.length+1) := supply ▸ reserveBinaryThinPayload_fits ceiling
    have initialInvariant : ∀ e ∈ G, (emptyFinThinLoads n).read e ≤ G.card.log2+1 := by
      rw [zero]
      exact fun _ _ => Nat.zero_le _
    obtain ⟨ending,_,values,invariant,⟨selected,selectedBits,selectedSet⟩,miss,count,work⟩ :=
      binaryThinRoundRunFromWithWork_refines arcs keys demands [] simple complete reachable code numeric bounded base
        ceiling factor size supply widthFits rows bounds matchLabels unique (emptyFinThinLoads n) start.1 encoded
        initialInvariant
    rw [zero] at values
    change ending.read = thinCoverRun G demands at values
    change selected.toFinset = round ending.read at selectedSet
    change run.1.rounded = _ at selectedBits
    change run.1.missed = thinRoundRunMissFrom G round demands (emptyFinThinLoads n).read at miss
    have failure : run.1.missed = true ↔ ThinRoundFailure G factorValue sample demands := by
      rw [miss,zero,sameRound,thinRoundRunMissFrom_eq_true_iff]
      rfl
    have result : ∃ kept : List (Fin n × Fin n), (if run.1.missed then arcBits else run.1.rounded) =
        binaryEncodeArcs code kept ∧ kept.toFinset = thinRoundRun G factorValue sample demands := by
      by_cases missed : run.1.missed = true
      · refine ⟨arcs,by simp [missed,arcBits],?_⟩
        have failureAtSomePrefix := failure.mp missed
        change arcs.toFinset = if demands.isEmpty then ∅ else if ThinRoundFailure G factorValue sample demands then G
          else roundedThinArcs G factorValue (thinCoverRun G demands) sample
        simp [demands,failureAtSomePrefix,G]
      · refine ⟨selected,by simp [missed,selectedBits],?_⟩
        have noPrefixFailure : ¬ ThinRoundFailure G factorValue sample demands := fun absent => missed (failure.mpr absent)
        rw [selectedSet,sameRound,values]
        simp [thinRoundRun,demands,noPrefixFailure]
    have countLimit : run.1.updates ≤ G.card*(G.card.log2+1) := by
      change loadTotal G (emptyFinThinLoads n).read+run.1.updates ≤ loadTotal G ending.read at count
      change ∀ e ∈ G, ending.read e ≤ G.card.log2+1 at invariant
      have total : loadTotal G ending.read ≤ G.card*(G.card.log2+1) := by
        unfold loadTotal
        exact (sum_le_sum invariant).trans_eq (by simp)
      omega
    have allocation : start.2 ≤ emptyBinaryThinLoadWorkBudget n (ceiling.length+1) base.length (ceiling.length+1) := by
      apply startCost.trans
      unfold emptyBinaryThinLoadWorkBudget
      gcongr
    have fullWork : run.2 ≤ binaryThinRoundRunWorkBudget n arcs.length keys.length rows.length base.length labels sampleWidth
        (ceiling.length+1) ceiling.length factor.length G.card demands.length (G.card*(G.card.log2+1)) := by
      change run.2 ≤ binaryThinRoundRunWorkBudget n arcs.length keys.length rows.length base.length labels sampleWidth
        (ceiling.length+1) ceiling.length factor.length G.card demands.length run.1.updates at work
      apply work.trans
      unfold binaryThinRoundRunWorkBudget
      gcongr
    refine ⟨result,?_⟩
    change width.2+start.2+run.2+6 ≤ _
    unfold binaryThinRoundFromEmptyWorkBudget
    exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add widthCost allocation) fullWork) 6

private theorem binaryThinRoundRunFromWithWork_rounded_length_le {n : ℕ} (arcs keys : List (List Bool × List Bool))
    (base ceiling factor : List Bool) (rows : List (BinaryThinThresholdRow n)) (depth supply fuel : ℕ)
    (demands : List (List Bool × List Bool)) (cells : List (List Bool)) (prior : List (List Bool × List Bool))
    (fits : prior.length ≤ rows.length) :
    (binaryThinRoundRunFromWithWork arcs keys base ceiling factor rows depth supply fuel demands cells prior).1.rounded.length ≤
      rows.length := by
  induction demands generalizing cells prior with
  | nil => exact fits
  | cons demand rest ih =>
    let first := binaryThinDemandWithWork arcs keys base ceiling factor cells rows demand.1 demand.2 depth supply fuel
    have enough : first.1.rounded.length ≤ rows.length :=
      roundBinaryThinEncodedRowsWithWork_length_le base factor _ rows
    exact ih first.1.cells first.1.rounded enough

/-- The fallback can return the original arcs. Without it each output
row comes from the supplied threshold cache. -/
theorem binaryThinRoundRunWithWork_length_le {n : ℕ} (arcs keys : List (List Bool × List Bool))
    (base ceiling factor : List Bool) (rows : List (BinaryThinThresholdRow n)) (depth supply fuel : ℕ)
    (demands : List (List Bool × List Bool)) :
    (binaryThinRoundRunWithWork arcs keys base ceiling factor rows depth supply fuel demands).1.length ≤
      max arcs.length rows.length := by
  unfold binaryThinRoundRunWithWork
  split
  · exact Nat.zero_le _
  · dsimp only
    split
    · exact le_max_left _ _
    · exact (binaryThinRoundRunFromWithWork_rounded_length_le arcs keys base ceiling factor rows depth supply fuel
        demands _ [] (Nat.zero_le _)).trans (le_max_right _ _)

end OnlineReachabilityPreservers
