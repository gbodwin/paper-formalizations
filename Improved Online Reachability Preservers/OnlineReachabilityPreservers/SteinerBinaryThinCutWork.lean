import OnlineReachabilityPreservers.SteinerBinaryIntervalWork
import OnlineReachabilityPreservers.SteinerBinaryThinCapacityWork
import OnlineReachabilityPreservers.SteinerClippedFlowCut

/-! The thin separator on a prepared interval and the current binary load table. -/

namespace OnlineReachabilityPreservers

open Finset

/-- Form the clipped capacities from the current load cells, then find the
violating cut on the supplied interval arcs. -/
def binaryPreparedThinCutWithWork (active keys : List (List Bool × List Bool))
    (base ceiling : List Bool) (cells : List (List Bool)) (source target : List Bool) (depth supply : ℕ) :
    Option (List (List Bool × List Bool)) × ℕ :=
  let self := binaryEqualWithWork source target
  if self.1 then (none,self.2+4) else
    let capacities := binaryThinCapacityRowsWithWork active base ceiling cells keys
    let cut := binaryFindLowCapacityOutgoingCutWithWork active capacities.1 source target depth supply
    (cut.1,self.2+capacities.2+cut.2+7)

/-- The graph interval is supplied. The tally covers the binary capacity
scan and the exact bounded cut search on that interval. -/
def binaryPreparedThinCutWorkBudget (n active keys base labels loadWidth ceilingWidth supply : ℕ) : ℕ :=
  (5*labels+3)+binaryThinCapacityRowsWorkBudget n active keys base labels loadWidth ceilingWidth+
    binaryLowCapacityOutgoingCutWorkBudget n active keys labels ceilingWidth supply+7

private theorem localArcCapacity_clip_eq {n : ℕ} (G : Arcs (Fin n)) (demand : Fin n × Fin n)
    (load : CutLoads (Fin n)) :
    clippedThinArcCapacity (intervalArcs G demand) load G.card =
      fun arc => min (localArcCapacity G demand load arc) (G.card : ℤ) := by
  funext arc
  by_cases within : arc ∈ intervalArcs G demand
  · simp [clippedThinArcCapacity,localArcCapacity,within]
  · simp [clippedThinArcCapacity,localArcCapacity,within]

private theorem outgoingCut_insideInterval_eq {n : ℕ} (G : Arcs (Fin n)) (demand : Fin n × Fin n)
    (side : Finset (Fin n)) :
    outgoingCut (intervalArcs G demand) side =
      outgoingCut (intervalArcs G demand) (side ∩ reachInterval G demand) := by
  ext arc
  by_cases inside : arc ∈ intervalArcs G demand
  · obtain ⟨first,last⟩ := (mem_filter.mp inside).2
    simp [outgoingCut,inside,first,last]
  · simp [outgoingCut,inside]

/-- The binary separator returns the original thin cut's arc set from
the supplied interval, complete pair enumeration, and matching load table. -/
theorem binaryPreparedThinCutWithWork_refines {n labels width : ℕ}
    (G : Arcs (Fin n)) (demand : Fin n × Fin n) (table : FinThinLoadTable n)
    (code : Fin n → List Bool) (numeric : ∀ v, binaryWordValue (code v) = v.val)
    (bounded : ∀ v, (code v).length ≤ labels) (active keys : List (Fin n × Fin n))
    (interval : active.toFinset = intervalArcs G demand) (complete : ∀ e, e ∈ keys)
    (base ceiling : List Bool) (size : binaryWordValue base = n) (supply : binaryWordValue ceiling = G.card)
    (cells : List (List Bool)) (encoded : EncodesThinLoadTable table cells width) :
    let out := binaryPreparedThinCutWithWork (binaryEncodeArcs code active) (binaryEncodeArcs code keys)
      base ceiling cells (code demand.1) (code demand.2) n G.card
    (match fastThinViolation G demand table.read with
      | none => out.1 = none
      | some side =>
        ∃ cut : List (Fin n × Fin n), out.1 = some (binaryEncodeArcs code cut) ∧
          cut.toFinset = outgoingCut (intervalArcs G demand) side ∧ (active.Nodup → cut.Nodup)) ∧
      out.2 ≤ binaryPreparedThinCutWorkBudget n active.length keys.length base.length labels width ceiling.length G.card := by
  have injective : Function.Injective code := fun a b equal =>
    Fin.ext ((numeric a).symm.trans ((congrArg binaryWordValue equal).trans (numeric b)))
  let aBits := binaryEncodeArcs code active
  let keyBits := binaryEncodeArcs code keys
  let self := binaryEqualWithWork (code demand.1) (code demand.2)
  let measured := binaryThinCapacityRowsWithWork aBits base ceiling cells keyBits
  let cut := binaryFindLowCapacityOutgoingCutWithWork aBits measured.1 (code demand.1) (code demand.2) n G.card
  let output := if self.1 then ((none : Option (List (List Bool × List Bool))),self.2+4)
      else (cut.1,self.2+measured.2+cut.2+7)
  obtain ⟨selfValue,selfWork⟩ := binaryEqualWithWork_spec (code demand.1) (code demand.2)
  have selfBound := selfWork.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ (bounded demand.1)) _)
  change self.1 = _ at selfValue
  change self.2 ≤ 5*labels+3 at selfBound
  change (match fastThinViolation G demand table.read with
      | none => output.1 = none
      | some side =>
        ∃ c : List (Fin n × Fin n), output.1 = some (binaryEncodeArcs code c) ∧
          c.toFinset = outgoingCut (intervalArcs G demand) side ∧ (active.Nodup → c.Nodup)) ∧
    output.2 ≤ binaryPreparedThinCutWorkBudget n active.length keys.length base.length labels width ceiling.length G.card
  unfold output
  rw [selfValue]
  by_cases same : demand.1 = demand.2
  · have referenceSelf : fastThinViolation G demand table.read = none := by simp [fastThinViolation,same]
    rw [referenceSelf,decide_eq_true (congrArg code same)]
    refine ⟨rfl,?_⟩
    change self.2+4 ≤ _
    unfold binaryPreparedThinCutWorkBudget
    omega
  · have different : code demand.1 ≠ code demand.2 := fun h => same (injective h)
    simp only [decide_eq_false different,Bool.false_eq_true,ite_false]
    obtain ⟨rows,rowValue,rowKeys,capacities,rowCost⟩ := binaryThinCapacityRowsWithWork_spec table code numeric bounded
      active keys base ceiling size cells encoded
    let clipped := clippedThinArcCapacity active.toFinset table.read (binaryWordValue ceiling)
    have completeRows (e : Fin n × Fin n) : e ∈ rows.map Prod.fst := rowKeys.symm ▸ complete e
    have length : rows.length = keys.length := by simpa only [List.length_map] using congrArg List.length rowKeys
    obtain ⟨agreement,cutCost⟩ := binaryFindLowCapacityOutgoingCutWithWork_refines
      (capacity := clipped) code injective labels bounded active rows demand.1 demand.2 ceiling.length G.card
      completeRows capacities
    change measured.1 = _ at rowValue
    change measured.2 ≤ _ at rowCost
    simp only [Fintype.card_fin,← rowValue,length] at agreement cutCost
    refine ⟨?_,?_⟩
    · have original : clipped = fun e => min (localArcCapacity G demand table.read e) (G.card : ℤ) := by
        unfold clipped
        rw [interval,supply]
        exact localArcCapacity_clip_eq G demand table.read
      have nonnegative (e : Fin n × Fin n) : 0 ≤ localArcCapacity G demand table.read e := by
        unfold localArcCapacity
        split
        · positivity
        · exact le_rfl
      rw [original,findLowCapacityCut_clip_to_supply (localArcCapacity G demand table.read)
        demand.1 demand.2 G.card nonnegative] at agreement
      rw [fastThinViolation_eq_lowCut G demand table.read same]
      cases selected : findLowCapacityCut (localArcCapacity G demand table.read) demand.1 demand.2 G.card with
      | none =>
        rw [selected] at agreement
        exact agreement
      | some side =>
        rw [selected] at agreement
        obtain ⟨chosen,encodedCut,fits,simple⟩ := agreement
        refine ⟨chosen,encodedCut,?_,simple⟩
        rw [fits,interval]
        exact outgoingCut_insideInterval_eq G demand side
    · exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add selfBound rowCost) cutCost) _

/-- Compute the interval from the original encoded arcs before searching
for a violating thin cut in the supplied load table. -/
def binaryThinCutWithWork (arcs keys : List (List Bool × List Bool))
    (base ceiling : List Bool) (cells : List (List Bool)) (source target : List Bool) (depth supply : ℕ) :
    Option (List (List Bool × List Bool)) × ℕ :=
  let active := binaryDemandIntervalArcsWithWork arcs source target depth
  let cut := binaryPreparedThinCutWithWork active.1 keys base ceiling cells source target depth supply
  (cut.1,active.2+cut.2+4)

/-- The original graph and binary load table determine an exact reference
thin cut. The work uses a restricted arc list no larger than the input. -/
theorem binaryThinCutWithWork_refines {n labels width : ℕ}
    (arcs keys : List (Fin n × Fin n)) (demand : Fin n × Fin n) (table : FinThinLoadTable n)
    (code : Fin n → List Bool) (numeric : ∀ v, binaryWordValue (code v) = v.val)
    (bounded : ∀ v, (code v).length ≤ labels) (complete : ∀ e, e ∈ keys)
    (base ceiling : List Bool) (size : binaryWordValue base = n)
    (supply : binaryWordValue ceiling = arcs.toFinset.card)
    (cells : List (List Bool)) (encoded : EncodesThinLoadTable table cells width) :
    let graph := arcs.toFinset
    let active := arcs.filter fun e => decide (e ∈ intervalArcs graph demand)
    let out := binaryThinCutWithWork (binaryEncodeArcs code arcs) (binaryEncodeArcs code keys)
      base ceiling cells (code demand.1) (code demand.2) n graph.card
    (match fastThinViolation graph demand table.read with
      | none => out.1 = none
      | some side =>
        ∃ cut : List (Fin n × Fin n), out.1 = some (binaryEncodeArcs code cut) ∧
          cut.toFinset = outgoingCut (intervalArcs graph demand) side ∧ (arcs.Nodup → cut.Nodup)) ∧
      out.2 ≤ binaryDemandIntervalArcsWorkBudget n arcs.length labels n+
        binaryPreparedThinCutWorkBudget n active.length keys.length base.length labels width ceiling.length graph.card+4 := by
  have injective : Function.Injective code := fun a b equal =>
    Fin.ext ((numeric a).symm.trans ((congrArg binaryWordValue equal).trans (numeric b)))
  let graph := arcs.toFinset
  let active := arcs.filter fun e => decide (e ∈ intervalArcs graph demand)
  let interval := binaryDemandIntervalArcsWithWork (binaryEncodeArcs code arcs) (code demand.1) (code demand.2) n
  have sameSet : active.toFinset = intervalArcs graph demand := by
    ext e
    simp only [active,List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
    exact ⟨And.right,fun present => ⟨List.mem_toFinset.mp (intervalArcs_subset _ _ present),present⟩⟩
  obtain ⟨intervalValue,intervalCost⟩ := binaryDemandIntervalArcsWithWork_spec code injective labels bounded arcs demand
  simp only [Fintype.card_fin] at intervalValue intervalCost
  change interval.1 = binaryEncodeArcs code active at intervalValue
  change interval.2 ≤ _ at intervalCost
  obtain ⟨value,work⟩ := binaryPreparedThinCutWithWork_refines graph demand table code numeric bounded
    active keys sameSet complete base ceiling size supply cells encoded
  rw [← intervalValue] at value work
  unfold binaryThinCutWithWork
  refine ⟨?_,Nat.add_le_add_right (Nat.add_le_add intervalCost work) _⟩
  cases reply : fastThinViolation graph demand table.read with
  | none =>
    rw [reply] at value
    exact value
  | some side =>
    rw [reply] at value
    obtain ⟨cut,encodedCut,cutSet,simple⟩ := value
    exact ⟨cut,encodedCut,cutSet,fun distinct => simple (List.filter_sublist.nodup distinct)⟩

end OnlineReachabilityPreservers
