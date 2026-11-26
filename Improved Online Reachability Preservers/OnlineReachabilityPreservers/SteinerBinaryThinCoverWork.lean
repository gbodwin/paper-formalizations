import OnlineReachabilityPreservers.SteinerBinaryThinLoopWork
import OnlineReachabilityPreservers.SteinerThinBitInitializationWork

/-! An encoded chronological run of the fractional thin-demand phase. -/

namespace OnlineReachabilityPreservers

open Finset

/-- Reuse the encoded graph and table across the demand list. Each demand
gets its own interval and a complete cut loop before the next demand. -/
def binaryThinCoverTraceFromWithWork (arcs keys : List (List Bool × List Bool))
    (base ceiling : List Bool) (depth supply fuel : ℕ) :
    List (List Bool × List Bool) → List (List Bool) → (List (List Bool) × ℕ) × ℕ
  | [], cells => ((cells,0),2)
  | demand::rest, cells =>
    let first := binaryThinLoopWithWork arcs keys base ceiling demand.1 demand.2 depth supply fuel cells
    let tail := binaryThinCoverTraceFromWithWork arcs keys base ceiling depth supply fuel rest first.1.1
    ((tail.1.1,first.1.2+tail.1.2),first.2+tail.2+6)

def binaryThinCoverTraceWorkBudget (n arcs keys base labels width ceiling supply demands updates : ℕ) : ℕ :=
  (demands+updates)*binaryPreparedThinLoopStepWorkBudget n arcs keys base labels width ceiling supply+
    demands*(binaryDemandIntervalArcsWorkBudget n arcs labels n+12)+2

theorem binaryPreparedThinLoopStepWorkBudget_le_arcs
    (n keys base labels width ceiling supply : ℕ) {smaller larger : ℕ} (fits : smaller ≤ larger) :
    binaryPreparedThinLoopStepWorkBudget n smaller keys base labels width ceiling supply ≤
      binaryPreparedThinLoopStepWorkBudget n larger keys base labels width ceiling supply := by
  have capacities := binaryThinCapacityRowsWorkBudget_mono_active n keys base labels width ceiling fits
  have separator : binaryLowCapacityOutgoingCutWorkBudget n smaller keys labels ceiling supply ≤
      binaryLowCapacityOutgoingCutWorkBudget n larger keys labels ceiling supply := by
    unfold binaryLowCapacityOutgoingCutWorkBudget binaryFlowCutWorkBudget binaryResidualCutWorkBudget
    dsimp
    gcongr
  unfold binaryPreparedThinLoopStepWorkBudget binaryPreparedThinCutWorkBudget
  exact Nat.add_le_add_right
    (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add_left capacities _) separator) _) _) _

/-- The table represents the chronological fractional updates exactly.
Successful cuts consume units of the same total-load potential as the
reference, so the work can be bounded by their total across all arrivals. -/
theorem binaryThinCoverTraceFromWithWork_refines {n labels width : ℕ}
    (arcs keys demands : List (Fin n × Fin n)) (simple : arcs.Nodup) (complete : ∀ e, e ∈ keys)
    (reachable : ∀ demand ∈ demands, Reach arcs.toFinset demand.1 demand.2)
    (code : Fin n → List Bool) (numeric : ∀ v, binaryWordValue (code v) = v.val)
    (bounded : ∀ v, (code v).length ≤ labels) (base ceiling : List Bool)
    (size : binaryWordValue base = n) (supply : binaryWordValue ceiling = arcs.toFinset.card)
    (widthFits : arcs.toFinset.card.log2+1 < 2^width)
    (table : FinThinLoadTable n) (cells : List (List Bool))
    (encoded : EncodesThinLoadTable table cells width)
    (invariant : ∀ e ∈ arcs.toFinset, table.read e ≤ arcs.toFinset.card.log2+1) :
    let graph := arcs.toFinset
    let fuel := graph.card*(graph.card.log2+1)+1
    let out := binaryThinCoverTraceFromWithWork (binaryEncodeArcs code arcs) (binaryEncodeArcs code keys)
      base ceiling n graph.card fuel (binaryEncodeArcs code demands) cells
    ∃ ending : FinThinLoadTable n, EncodesThinLoadTable ending out.1.1 width ∧
      ending.read = demands.foldl (fun loads demand => thinCoverStep graph demand loads) table.read ∧
      (∀ e ∈ graph, ending.read e ≤ graph.card.log2+1) ∧
      loadTotal graph table.read+out.1.2 ≤ loadTotal graph ending.read ∧
      out.2 ≤ binaryThinCoverTraceWorkBudget n arcs.length keys.length base.length labels width ceiling.length
        graph.card demands.length out.1.2 := by
  let graph := arcs.toFinset
  let fuel := graph.card*(graph.card.log2+1)+1
  let step := binaryPreparedThinLoopStepWorkBudget n arcs.length keys.length base.length labels width
    ceiling.length graph.card
  let prepared := binaryDemandIntervalArcsWorkBudget n arcs.length labels n
  let arcBits := binaryEncodeArcs code arcs
  let keyBits := binaryEncodeArcs code keys
  induction demands generalizing table cells with
  | nil =>
    refine ⟨table,encoded,rfl,invariant,?_,?_⟩
    · simp [binaryThinCoverTraceFromWithWork,binaryEncodeArcs]
    · simp [binaryThinCoverTraceFromWithWork,binaryEncodeArcs,binaryThinCoverTraceWorkBudget]
  | cons demand tail ih =>
    let first := binaryThinLoopWithWork arcBits keyBits base ceiling (code demand.1) (code demand.2)
      n graph.card fuel cells
    let active := arcs.filter fun e => decide (e ∈ intervalArcs graph demand)
    let activeStep := binaryPreparedThinLoopStepWorkBudget n active.length keys.length base.length labels width
      ceiling.length graph.card
    have request := reachable demand List.mem_cons_self
    obtain ⟨next,nextEncoding,nextLoads,nextCount,nextInvariant,nextCost⟩ := binaryThinLoopWithWork_refines
      arcs keys demand request simple complete code numeric bounded base ceiling size supply widthFits fuel table cells
      encoded invariant
    change EncodesThinLoadTable next first.1.1 width at nextEncoding
    change next.read = (thinCoverLoop graph demand fuel table.read).1 at nextLoads
    change first.1.2 = (thinCoverLoop graph demand fuel table.read).2 at nextCount
    change first.2 ≤ prepared+(first.1.2+1)*activeStep+6 at nextCost
    have stepFits : activeStep ≤ step :=
      binaryPreparedThinLoopStepWorkBudget_le_arcs n keys.length base.length labels width ceiling.length graph.card
        (List.length_filter_le _ _)
    have firstCost : first.2 ≤ prepared+(first.1.2+1)*step+6 :=
      nextCost.trans (by gcongr)
    have conforms : next.read = thinCoverStep graph demand table.read := nextLoads
    have progress : loadTotal graph table.read+first.1.2 ≤ loadTotal graph next.read := by
      rw [nextCount,nextLoads]
      exact thinCoverLoop_load_progress graph graph Subset.rfl demand request fuel table.read invariant
    obtain ⟨ending,lastEncoding,lastLoads,lastInvariant,lastProgress,lastCost⟩ :=
      ih (fun d present => reachable d (List.mem_cons_of_mem _ present)) next first.1.1 nextEncoding nextInvariant
    let rest := binaryThinCoverTraceFromWithWork arcBits keyBits base ceiling n graph.card fuel
      (binaryEncodeArcs code tail) first.1.1
    change EncodesThinLoadTable ending rest.1.1 width at lastEncoding
    change loadTotal graph next.read+rest.1.2 ≤ loadTotal graph ending.read at lastProgress
    change rest.2 ≤ (tail.length+rest.1.2)*step+tail.length*(prepared+12)+2 at lastCost
    rw [conforms] at lastLoads
    refine ⟨ending,lastEncoding,lastLoads,lastInvariant,?_,?_⟩
    · change loadTotal graph table.read+(first.1.2+rest.1.2) ≤ loadTotal graph ending.read
      omega
    · change first.2+rest.2+6 ≤
        (tail.length+1+(first.1.2+rest.1.2))*step+(tail.length+1)*(prepared+12)+2
      simp only [Nat.add_mul,Nat.one_mul] at firstCost lastCost ⊢
      omega

def reserveBinaryThinPayloadWithWork (ceiling : List Bool) : List Bool × ℕ :=
  let length := binaryWordLengthWithWork ceiling
  let extra := addBinaryWordsWithWork length.1 [] true
  (extra.1,length.2+extra.2+4)

def reserveBinaryThinPayloadWorkBudget (ceiling : ℕ) : ℕ :=
  (3+ceiling*(20*ceiling+9))+(20*ceiling+5)+4

theorem reserveBinaryThinPayloadWithWork_spec (ceiling : List Bool) :
    let out := reserveBinaryThinPayloadWithWork ceiling
    binaryWordValue out.1 = ceiling.length+1 ∧ out.1.length ≤ ceiling.length+1 ∧
      out.2 ≤ reserveBinaryThinPayloadWorkBudget ceiling.length := by
  let length := binaryWordLengthWithWork ceiling
  let extra := addBinaryWordsWithWork length.1 [] true
  obtain ⟨decoded,stored,work⟩ := binaryWordLengthWithWork_spec ceiling
  obtain ⟨value,narrow,spent⟩ := addBinaryWordsWithWork_spec length.1 [] true
  change binaryWordValue length.1 = _ at decoded
  change length.1.length ≤ _ at stored
  change length.2 ≤ _ at work
  change binaryWordValue extra.1 = binaryWordValue length.1+0+1 at value
  change extra.1.length ≤ length.1.length+0+1 at narrow
  change extra.2 ≤ 20*(length.1.length+0)+5 at spent
  change binaryWordValue extra.1 = _ ∧ extra.1.length ≤ _ ∧ length.2+extra.2+4 ≤ _
  unfold reserveBinaryThinPayloadWorkBudget
  refine ⟨by simpa only [decoded,Nat.add_zero] using value,by omega,by omega⟩

theorem reserveBinaryThinPayload_fits (ceiling : List Bool) :
    (binaryWordValue ceiling).log2+1 < 2^(ceiling.length+1) := by
  have below := binaryWordValue_lt_pow ceiling
  have grows : 2^ceiling.length < 2^(ceiling.length+1) :=
    Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _)
  exact ((Nat.add_le_add_right (Nat.log2_le_self _) 1).trans (Nat.succ_le_of_lt below)).trans_lt grows

/-- Allocate a binary zero table with sufficient payload width, then run
the chronological fractional updates. -/
def binaryThinCoverFromEmptyWithWork (arcs keys : List (List Bool × List Bool))
    (base ceiling : List Bool) (depth supply fuel : ℕ) (demands : List (List Bool × List Bool)) :
    (List (List Bool) × ℕ) × ℕ :=
  let width := reserveBinaryThinPayloadWithWork ceiling
  let start := emptyBinaryThinLoadsWithWork base width.1
  let run := binaryThinCoverTraceFromWithWork arcs keys base ceiling depth supply fuel demands start.1
  (run.1,width.2+start.2+run.2+4)

def binaryThinCoverFromEmptyWorkBudget (n arcs keys base labels ceiling supply demands updates : ℕ) : ℕ :=
  reserveBinaryThinPayloadWorkBudget ceiling+emptyBinaryThinLoadWorkBudget n (ceiling+1) base (ceiling+1)+
    binaryThinCoverTraceWorkBudget n arcs keys base labels (ceiling+1) ceiling supply demands updates+4

/-- From its own empty table, the run represents the paper's fractional
thin cover on the supplied graph and feasible chronological requests. -/
theorem binaryThinCoverFromEmptyWithWork_refines {n labels : ℕ}
    (arcs keys demands : List (Fin n × Fin n)) (simple : arcs.Nodup) (complete : ∀ e, e ∈ keys)
    (reachable : ∀ demand ∈ demands, Reach arcs.toFinset demand.1 demand.2)
    (code : Fin n → List Bool) (numeric : ∀ v, binaryWordValue (code v) = v.val)
    (bounded : ∀ v, (code v).length ≤ labels) (base ceiling : List Bool)
    (size : binaryWordValue base = n) (supply : binaryWordValue ceiling = arcs.toFinset.card) :
    let graph := arcs.toFinset
    let fuel := graph.card*(graph.card.log2+1)+1
    let out := binaryThinCoverFromEmptyWithWork (binaryEncodeArcs code arcs) (binaryEncodeArcs code keys)
      base ceiling n graph.card fuel (binaryEncodeArcs code demands)
    ∃ ending : FinThinLoadTable n, EncodesThinLoadTable ending out.1.1 (ceiling.length+1) ∧
      ending.read = thinCoverRun graph demands ∧ out.1.2 ≤ graph.card*(graph.card.log2+1) ∧
      out.2 ≤ binaryThinCoverFromEmptyWorkBudget n arcs.length keys.length base.length labels ceiling.length
        graph.card demands.length out.1.2 := by
  let graph := arcs.toFinset
  let fuel := graph.card*(graph.card.log2+1)+1
  let width := reserveBinaryThinPayloadWithWork ceiling
  let start := emptyBinaryThinLoadsWithWork base width.1
  let run := binaryThinCoverTraceFromWithWork (binaryEncodeArcs code arcs) (binaryEncodeArcs code keys)
    base ceiling n graph.card fuel (binaryEncodeArcs code demands) start.1
  obtain ⟨decoded,short,widthCost⟩ := reserveBinaryThinPayloadWithWork_spec ceiling
  change binaryWordValue width.1 = _ at decoded
  change width.1.length ≤ _ at short
  change width.2 ≤ _ at widthCost
  obtain ⟨encoded,startCost⟩ := emptyBinaryThinLoadsWithWork_spec base width.1 size
  change EncodesThinLoadTable (emptyFinThinLoads n) start.1 (binaryWordValue width.1) at encoded
  change start.2 ≤ _ at startCost
  rw [decoded] at encoded startCost
  have widthFits : graph.card.log2+1 < 2^(ceiling.length+1) :=
    supply ▸ reserveBinaryThinPayload_fits ceiling
  have zero : (emptyFinThinLoads n).read = fun _ => 0 := by
    funext e
    simp [FinThinLoadTable.read,emptyFinThinLoads]
  have initialInvariant : ∀ e ∈ graph, (emptyFinThinLoads n).read e ≤ graph.card.log2+1 := by
    rw [zero]
    exact fun _ _ => Nat.zero_le _
  obtain ⟨ending,encoding,values,invariant,count,work⟩ := binaryThinCoverTraceFromWithWork_refines arcs keys demands
    simple complete reachable code numeric bounded base ceiling size supply widthFits (emptyFinThinLoads n) start.1
    encoded initialInvariant
  rw [zero] at values
  change loadTotal graph (emptyFinThinLoads n).read+run.1.2 ≤ loadTotal graph ending.read at count
  change ∀ e ∈ graph, ending.read e ≤ graph.card.log2+1 at invariant
  have total : loadTotal graph ending.read ≤ graph.card*(graph.card.log2+1) := by
    unfold loadTotal
    exact (sum_le_sum invariant).trans_eq (by simp)
  have initialBound : start.2 ≤ emptyBinaryThinLoadWorkBudget n (ceiling.length+1) base.length (ceiling.length+1) := by
    apply startCost.trans
    unfold emptyBinaryThinLoadWorkBudget
    gcongr
  refine ⟨ending,encoding,values,?_,?_⟩
  · change run.1.2 ≤ graph.card*(graph.card.log2+1)
    omega
  · unfold binaryThinCoverFromEmptyWorkBudget
    exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add widthCost initialBound) work) 4

end OnlineReachabilityPreservers
