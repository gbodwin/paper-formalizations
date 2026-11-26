import OnlineReachabilityPreservers.SteinerBinaryThinCutWork

/-! Generate and apply every cut for one thin demand on the binary load table. -/

namespace OnlineReachabilityPreservers

open Finset

/-- Rebuild capacities from the current table on each cut test. The interval
and pair keys are prepared once and shared by the whole loop. -/
def binaryPreparedThinLoopWithWork (active keys : List (List Bool × List Bool))
    (base ceiling source target : List Bool) (depth supply : ℕ) :
    ℕ → List (List Bool) → (List (List Bool) × ℕ) × ℕ
  | 0, cells => ((cells,0),2)
  | fuel+1, cells =>
    let separated := binaryPreparedThinCutWithWork active keys base ceiling cells source target depth supply
    match separated.1 with
    | none => ((cells,0),separated.2+4)
    | some cut =>
      let updated := bumpBinaryThinCutWithWork base cells cut
      let tail := binaryPreparedThinLoopWithWork active keys base ceiling source target depth supply fuel updated.1
      ((tail.1.1,tail.1.2+1),separated.2+updated.2+tail.2+8)

/-- A cut test, a possible load update on at most the graph's arc count,
and the surrounding list operations. -/
def binaryPreparedThinLoopStepWorkBudget (n active keys base labels payload ceiling supply : ℕ) : ℕ :=
  binaryPreparedThinCutWorkBudget n active keys base labels payload ceiling supply+
    (3+supply*(binaryThinLoadBumpWorkBudget (n*n) base labels payload+5))+8

private theorem binaryCutLabelsMatch {n labels : ℕ} (code : Fin n → List Bool)
    (numeric : ∀ v, binaryWordValue (code v) = v.val) (bounded : ∀ v, (code v).length ≤ labels)
    (cut : List (Fin n × Fin n)) :
    List.Forall₂ (BinaryThinArcMatches labels) (binaryEncodeArcs code cut) cut := by
  induction cut with
  | nil => exact .nil
  | cons arc rest ih => exact .cons ⟨numeric _,numeric _,bounded _,bounded _⟩ ih

private theorem binaryLoadFits {n width : ℕ} (table : FinThinLoadTable n)
    (code : Fin n → List Bool) (numeric : ∀ v, binaryWordValue (code v) = v.val)
    (base : List Bool) (size : binaryWordValue base = n) (cells : List (List Bool))
    (encoded : EncodesThinLoadTable table cells width) (arc : Fin n × Fin n) :
    table.read arc < 2^width := by
  obtain ⟨⟨word,onCells,_,value⟩,_⟩ := thinLoadAccessWithBinaryWork_read_decoded table cells binaryWordValue arc
    base (code arc.1) (code arc.2) encoded.1 size (numeric arc.1) (numeric arc.2)
  rw [← value,← encoded.2 word onCells]
  exact binaryWordValue_lt_pow word

/-- On a feasible thin demand, the generated cuts give the precise reference
loads and update count. The work bound charges one test beyond the updates. -/
theorem binaryPreparedThinLoopWithWork_refines {n labels width : ℕ}
    (G : Arcs (Fin n)) (demand : Fin n × Fin n) (reachable : Reach G demand.1 demand.2)
    (active keys : List (Fin n × Fin n)) (interval : active.toFinset = intervalArcs G demand)
    (simple : active.Nodup) (complete : ∀ e, e ∈ keys)
    (code : Fin n → List Bool) (numeric : ∀ v, binaryWordValue (code v) = v.val)
    (bounded : ∀ v, (code v).length ≤ labels) (base ceiling : List Bool)
    (size : binaryWordValue base = n) (supply : binaryWordValue ceiling = G.card)
    (widthFits : G.card.log2+1 < 2^width)
    (fuel : ℕ) (table : FinThinLoadTable n) (cells : List (List Bool))
    (encoded : EncodesThinLoadTable table cells width)
    (invariant : ∀ e ∈ G, table.read e ≤ G.card.log2+1) :
    let out := binaryPreparedThinLoopWithWork (binaryEncodeArcs code active) (binaryEncodeArcs code keys)
      base ceiling (code demand.1) (code demand.2) n G.card fuel cells
    let ref := thinCoverLoop G demand fuel table.read
    ∃ ending : FinThinLoadTable n, EncodesThinLoadTable ending out.1.1 width ∧
      ending.read = ref.1 ∧ out.1.2 = ref.2 ∧ (∀ e ∈ G, ending.read e ≤ G.card.log2+1) ∧
      out.2 ≤ (out.1.2+1)*binaryPreparedThinLoopStepWorkBudget n active.length keys.length
        base.length labels width ceiling.length G.card+2 := by
  let budget := binaryPreparedThinLoopStepWorkBudget n active.length keys.length
    base.length labels width ceiling.length G.card
  let activeBits := binaryEncodeArcs code active
  let keyBits := binaryEncodeArcs code keys
  induction fuel generalizing table cells with
  | zero => exact ⟨table,encoded,rfl,rfl,invariant,by simp [binaryPreparedThinLoopWithWork]⟩
  | succ fuel ih =>
    let separated := binaryPreparedThinCutWithWork activeBits keyBits base ceiling cells
      (code demand.1) (code demand.2) n G.card
    obtain ⟨separatedValue,separatedCost⟩ := binaryPreparedThinCutWithWork_refines G demand table code numeric bounded
      active keys interval complete base ceiling size supply cells encoded
    change separated.2 ≤ _ at separatedCost
    rw [binaryPreparedThinLoopWithWork,thinCoverLoop]
    cases reply : fastThinViolation G demand table.read with
    | none =>
      rw [reply] at separatedValue
      change separated.1 = none at separatedValue
      rw [separatedValue]
      refine ⟨table,encoded,rfl,rfl,invariant,?_⟩
      change separated.2+4 ≤ (0+1)*budget+2
      unfold budget binaryPreparedThinLoopStepWorkBudget
      omega
    | some side =>
      rw [reply] at separatedValue
      obtain ⟨cut,cutValue,cutSet,cutSimple⟩ := separatedValue
      change separated.1 = some (binaryEncodeArcs code cut) at cutValue
      let referenceCut := outgoingCut (intervalArcs G demand) side
      let updated := bumpBinaryThinCutWithWork base cells (binaryEncodeArcs code cut)
      have unique := cutSimple simple
      have small : cutMass referenceCut table.read < G.card := (fastThinViolation_some reachable reply).2.2
      have newInvariant : ∀ e ∈ G, doubleCut referenceCut table.read e ≤ G.card.log2+1 :=
        doubleCut_bounded small invariant
      have sub : referenceCut ⊆ G :=
        (outgoingCut_subset _ _).trans (intervalArcs_subset _ _)
      have represent : cut.toFinset = referenceCut := cutSet
      have length : cut.length ≤ G.card := by
        rw [← List.toFinset_card_of_nodup unique,represent]
        exact card_le_card sub
      have fits (e : Fin n × Fin n) : table.read e+cut.count e < 2^width := by
        by_cases inCut : e ∈ cut
        · have present : e ∈ referenceCut := represent ▸ List.mem_toFinset.mpr inCut
          have amount := newInvariant e (sub present)
          rw [doubleCut,ite_eq_left present] at amount
          rw [List.count_eq_one_of_mem unique inCut]
          exact amount.trans_lt widthFits
        · rw [List.count_eq_zero_of_not_mem inCut,Nat.add_zero]
          exact binaryLoadFits table code numeric base size cells encoded e
      obtain ⟨⟨next,nextEncoding,filled⟩,updateWork⟩ := bumpBinaryThinCutWithWork_refines table cells base
        (binaryEncodeArcs code cut) cut encoded size (binaryCutLabelsMatch code numeric bounded cut) unique fits
      have nextLoads : next.read = doubleCut referenceCut table.read := by
        rw [filled,(bumpFinThinLoadsWithWordWork_spec table cut unique).1,represent]
      obtain ⟨ending,lastEncoding,lastLoads,lastCount,lastInvariant,lastCost⟩ :=
        ih next updated.1 nextEncoding (fun e member => nextLoads ▸ newInvariant e member)
      let tail := binaryPreparedThinLoopWithWork activeBits keyBits base ceiling (code demand.1) (code demand.2)
        n G.card fuel updated.1
      change EncodesThinLoadTable ending tail.1.1 width at lastEncoding
      change ending.read = (thinCoverLoop G demand fuel next.read).1 at lastLoads
      change tail.1.2 = (thinCoverLoop G demand fuel next.read).2 at lastCount
      change tail.2 ≤ (tail.1.2+1)*budget+2 at lastCost
      rw [nextLoads] at lastLoads lastCount
      have updateBound : updated.2 ≤ 3+G.card*(binaryThinLoadBumpWorkBudget (n*n) base.length labels width+5) :=
        updateWork.trans (by gcongr)
      rw [cutValue]
      refine ⟨ending,lastEncoding,lastLoads,congrArg (·+1) lastCount,lastInvariant,?_⟩
      change separated.2+updated.2+tail.2+8 ≤ (tail.1.2+1+1)*budget+2
      rw [Nat.succ_mul (tail.1.2+1)]
      dsimp [budget,binaryPreparedThinLoopStepWorkBudget] at lastCost ⊢
      omega

/-- Prepare the demand interval once from the original encoded graph,
then run all its load updates. -/
def binaryThinLoopWithWork (arcs keys : List (List Bool × List Bool))
    (base ceiling source target : List Bool) (depth supply fuel : ℕ) (cells : List (List Bool)) :
    (List (List Bool) × ℕ) × ℕ :=
  let active := binaryDemandIntervalArcsWithWork arcs source target depth
  let run := binaryPreparedThinLoopWithWork active.1 keys base ceiling source target depth supply fuel cells
  (run.1,active.2+run.2+4)

/-- With distinct original arc rows, the binary representation stays valid
and the final table and update count agree with the reference thin loop. -/
theorem binaryThinLoopWithWork_refines {n labels width : ℕ}
    (arcs keys : List (Fin n × Fin n)) (demand : Fin n × Fin n) (reachable : Reach arcs.toFinset demand.1 demand.2)
    (simple : arcs.Nodup) (complete : ∀ e, e ∈ keys)
    (code : Fin n → List Bool) (numeric : ∀ v, binaryWordValue (code v) = v.val)
    (bounded : ∀ v, (code v).length ≤ labels) (base ceiling : List Bool)
    (size : binaryWordValue base = n) (supply : binaryWordValue ceiling = arcs.toFinset.card)
    (widthFits : arcs.toFinset.card.log2+1 < 2^width)
    (fuel : ℕ) (table : FinThinLoadTable n) (cells : List (List Bool))
    (encoded : EncodesThinLoadTable table cells width)
    (invariant : ∀ e ∈ arcs.toFinset, table.read e ≤ arcs.toFinset.card.log2+1) :
    let graph := arcs.toFinset
    let active := arcs.filter fun e => decide (e ∈ intervalArcs graph demand)
    let out := binaryThinLoopWithWork (binaryEncodeArcs code arcs) (binaryEncodeArcs code keys)
      base ceiling (code demand.1) (code demand.2) n graph.card fuel cells
    let ref := thinCoverLoop graph demand fuel table.read
    ∃ ending : FinThinLoadTable n, EncodesThinLoadTable ending out.1.1 width ∧
      ending.read = ref.1 ∧ out.1.2 = ref.2 ∧ (∀ e ∈ graph, ending.read e ≤ graph.card.log2+1) ∧
      out.2 ≤ binaryDemandIntervalArcsWorkBudget n arcs.length labels n+
        (out.1.2+1)*binaryPreparedThinLoopStepWorkBudget n active.length keys.length
          base.length labels width ceiling.length graph.card+6 := by
  have injective : Function.Injective code := fun a b equal =>
    Fin.ext ((numeric a).symm.trans ((congrArg binaryWordValue equal).trans (numeric b)))
  let graph := arcs.toFinset
  let kept := arcs.filter fun e => decide (e ∈ intervalArcs graph demand)
  let active := binaryDemandIntervalArcsWithWork (binaryEncodeArcs code arcs) (code demand.1) (code demand.2) n
  have same : kept.toFinset = intervalArcs graph demand := by
    ext e
    simp only [kept,List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
    exact ⟨And.right,fun h => ⟨List.mem_toFinset.mp (intervalArcs_subset _ _ h),h⟩⟩
  obtain ⟨activeValue,activeCost⟩ := binaryDemandIntervalArcsWithWork_spec code injective labels bounded arcs demand
  simp only [Fintype.card_fin] at activeValue activeCost
  change active.1 = binaryEncodeArcs code kept at activeValue
  change active.2 ≤ _ at activeCost
  obtain ⟨ending,encoding,referenceLoads,count,keepInvariant,work⟩ := binaryPreparedThinLoopWithWork_refines graph
    demand reachable kept keys same (List.filter_sublist.nodup simple) complete code numeric bounded base ceiling size
    supply widthFits fuel table cells encoded invariant
  rw [← activeValue] at encoding count work
  refine ⟨ending,encoding,referenceLoads,count,keepInvariant,?_⟩
  let run := binaryPreparedThinLoopWithWork active.1 (binaryEncodeArcs code keys) base ceiling
    (code demand.1) (code demand.2) n graph.card fuel cells
  let step := binaryPreparedThinLoopStepWorkBudget n kept.length keys.length base.length labels width
    ceiling.length graph.card
  change run.2 ≤ (run.1.2+1)*step+2 at work
  change active.2+run.2+4 ≤ binaryDemandIntervalArcsWorkBudget n arcs.length labels n+(run.1.2+1)*step+6
  exact (Nat.add_le_add_right (Nat.add_le_add activeCost work) 4).trans_eq (by omega)

end OnlineReachabilityPreservers
