import OnlineReachabilityPreservers.SteinerBinaryArithmetic
import OnlineReachabilityPreservers.SteinerBinaryResidualCutWork

/-! Build residual arcs and extract their source cut from a supplied binary flow table. -/

namespace OnlineReachabilityPreservers

/-- A sign bit followed by a little-endian magnitude. Both zero signs denote zero. -/
structure BinarySignedWord where
  negative : Bool
  magnitude : List Bool

def BinarySignedWord.value (word : BinarySignedWord) : ℤ :=
  if word.negative then -(binaryWordValue word.magnitude : ℤ) else (binaryWordValue word.magnitude : ℤ)

/-- Test whether a signed flow word is strictly below an unsigned capacity. -/
def binaryFlowBelowCapacityWithWork (flow : BinarySignedWord) (capacity : List Bool) : Bool × ℕ :=
  if flow.negative then
    let zero := binaryZeroWithWork flow.magnitude
    if zero.1 then
      let emptyCapacity := binaryZeroWithWork capacity
      (!emptyCapacity.1,zero.2+emptyCapacity.2+8)
    else (true,zero.2+5)
  else
    let below := binaryLessWithWork flow.magnitude capacity false
    (below.1,below.2+5)

theorem binaryFlowBelowCapacityWithWork_spec (flow : BinarySignedWord) (capacity : List Bool) :
    let out := binaryFlowBelowCapacityWithWork flow capacity
    out.1 = decide (flow.value < (binaryWordValue capacity : ℤ)) ∧
      out.2 ≤ 14*(flow.magnitude.length+capacity.length)+14 := by
  rcases flow with ⟨negative,magnitude⟩
  cases negative with
  | false =>
    obtain ⟨value,work⟩ := binaryLessWithWork_noBorrow_spec magnitude capacity
    change (binaryLessWithWork magnitude capacity false).1 =
      decide ((binaryWordValue magnitude : ℤ) < (binaryWordValue capacity : ℤ)) ∧
      (binaryLessWithWork magnitude capacity false).2+5 ≤ 14*(magnitude.length+capacity.length)+14
    refine ⟨?_,?_⟩
    · rw [value,decide_eq_decide]
      omega
    · change (binaryLessWithWork magnitude capacity false).2 ≤ 14*(magnitude.length+capacity.length)+4 at work
      omega
  | true =>
    let zero := binaryZeroWithWork magnitude
    obtain ⟨zeroValue,zeroWork⟩ := binaryZeroWithWork_spec magnitude
    change zero.1 = decide (binaryWordValue magnitude = 0) at zeroValue
    change zero.2 ≤ 4*magnitude.length+3 at zeroWork
    change (if zero.1 then
        let cap := binaryZeroWithWork capacity
        (!cap.1,zero.2+cap.2+8)
      else (true,zero.2+5)).1 = decide (-(binaryWordValue magnitude : ℤ) < (binaryWordValue capacity : ℤ)) ∧
      (if zero.1 then
        let cap := binaryZeroWithWork capacity
        (!cap.1,zero.2+cap.2+8)
      else (true,zero.2+5)).2 ≤ 14*(magnitude.length+capacity.length)+14
    by_cases isZero : binaryWordValue magnitude = 0
    · rw [zeroValue,decide_eq_true isZero]
      obtain ⟨capValue,capWork⟩ := binaryZeroWithWork_spec capacity
      change (!(binaryZeroWithWork capacity).1) =
          decide (-(binaryWordValue magnitude : ℤ) < (binaryWordValue capacity : ℤ)) ∧
        zero.2+(binaryZeroWithWork capacity).2+8 ≤ 14*(magnitude.length+capacity.length)+14
      change (binaryZeroWithWork capacity).1 = decide (binaryWordValue capacity = 0) at capValue
      change (binaryZeroWithWork capacity).2 ≤ 4*capacity.length+3 at capWork
      refine ⟨?_,by omega⟩
      rw [capValue,isZero]
      by_cases empty : binaryWordValue capacity = 0
      · simp [empty]
      · rw [decide_eq_false empty]
        exact (decide_eq_true (by omega)).symm
    · rw [zeroValue,decide_eq_false isZero]
      change true = decide (-(binaryWordValue magnitude : ℤ) < (binaryWordValue capacity : ℤ)) ∧
        zero.2+5 ≤ 14*(magnitude.length+capacity.length)+14
      exact ⟨(decide_eq_true (by omega)).symm,by omega⟩

/-- One directed cell, with key, unsigned capacity, and signed flow. -/
structure BinaryCapacityFlowRow (Key : Type*) where
  arc : Key
  capacity : List Bool
  flow : BinarySignedWord

/-- Scan encoded cells and retain exactly the ordered arc labels with residual capacity. -/
def binaryResidualRowsWithWork :
    List (BinaryCapacityFlowRow (List Bool × List Bool)) → List (List Bool × List Bool) × ℕ
  | [] => ([],2)
  | row::rest =>
    let passes := binaryFlowBelowCapacityWithWork row.flow row.capacity
    let tail := binaryResidualRowsWithWork rest
    (if passes.1 then row.arc::tail.1 else tail.1,passes.2+tail.2+7)

/-- List visits, signed comparisons, and result construction for the supplied rows. -/
def binaryResidualRowsWorkBudget (rows capacityWidth flowWidth : ℕ) : ℕ :=
  2+rows*(14*(flowWidth+capacityWidth)+21)

variable {V : Type*}

/-- Describe the encoded input table using a common code for its vertices. -/
def binaryEncodeCapacityFlowRows (code : V → List Bool) (rows : List (BinaryCapacityFlowRow (V × V))) :
    List (BinaryCapacityFlowRow (List Bool × List Bool)) :=
  rows.map fun row => ⟨(code row.arc.1,code row.arc.2),row.capacity,row.flow⟩

/-- On decoded cells, the scan implements the exact reference comparison at each row. -/
theorem binaryResidualRowsWithWork_spec (code : V → List Bool) (capacity flow : ArcFlow V)
    (rows : List (BinaryCapacityFlowRow (V × V))) (capacityWidth flowWidth : ℕ)
    (decoded : ∀ row ∈ rows, (binaryWordValue row.capacity : ℤ) = capacity row.arc ∧
      row.flow.value = flow row.arc ∧ row.capacity.length ≤ capacityWidth ∧ row.flow.magnitude.length ≤ flowWidth) :
    let out := binaryResidualRowsWithWork (binaryEncodeCapacityFlowRows code rows)
    let arcs := rows.map BinaryCapacityFlowRow.arc
    out.1 = binaryEncodeArcs code (arcs.filter fun e => decide (flow e < capacity e)) ∧
      out.2 ≤ binaryResidualRowsWorkBudget rows.length capacityWidth flowWidth := by
  induction rows with
  | nil => simp [binaryEncodeCapacityFlowRows,binaryResidualRowsWithWork,binaryEncodeArcs,binaryResidualRowsWorkBudget]
  | cons row rest ih =>
    let test := binaryFlowBelowCapacityWithWork row.flow row.capacity
    let tail := binaryResidualRowsWithWork (binaryEncodeCapacityFlowRows code rest)
    let predicate := fun e : V × V => decide (flow e < capacity e)
    let perRow := 14*(flowWidth+capacityWidth)+21
    obtain ⟨capValue,flowValue,capSize,flowSize⟩ := decoded row List.mem_cons_self
    obtain ⟨testValue,testCost⟩ := binaryFlowBelowCapacityWithWork_spec row.flow row.capacity
    obtain ⟨tailValue,tailCost⟩ := ih (fun other present => decoded other (List.mem_cons_of_mem _ present))
    change test.1 = decide (row.flow.value < (binaryWordValue row.capacity : ℤ)) at testValue
    rw [flowValue,capValue] at testValue
    change tail.1 = _ at tailValue
    change test.2 ≤ 14*(row.flow.magnitude.length+row.capacity.length)+14 at testCost
    change tail.2 ≤ 2+rest.length*perRow at tailCost
    change (if test.1 then (code row.arc.1,code row.arc.2)::tail.1 else tail.1) =
        binaryEncodeArcs code (((row::rest).map BinaryCapacityFlowRow.arc).filter predicate) ∧
      test.2+tail.2+7 ≤ 2+(rest.length+1)*perRow
    refine ⟨?_,?_⟩
    · rw [List.map_cons,List.filter_cons,testValue,tailValue]
      split <;> rfl
    · dsimp [perRow] at tailCost ⊢
      rw [Nat.succ_mul rest.length]
      omega

/-- Build the residual arcs from the encoded flow table and extract the
outgoing cut of the supplied original arcs at the given search depth. -/
def binaryFlowCutWithWork (arcs : List (List Bool × List Bool))
    (rows : List (BinaryCapacityFlowRow (List Bool × List Bool))) (source : List Bool) (depth : ℕ) :
    List (List Bool × List Bool) × ℕ :=
  let residual := binaryResidualRowsWithWork rows
  let cut := binaryResidualCutWithWork arcs residual.1 source depth
  (cut.1,residual.2+cut.2+4)

/-- Every residual arc comes from one table row, so the row count bounds the search input. -/
def binaryFlowCutWorkBudget (n arcs rows labels capacityWidth flowWidth depth : ℕ) : ℕ :=
  binaryResidualRowsWorkBudget rows capacityWidth flowWidth+binaryResidualCutWorkBudget n arcs rows labels depth+4

/-- A complete table of supplied signed flow and unsigned capacity words
gives exactly the reference cut, with a polynomial list-and-bit work bound. -/
theorem binaryFlowCutWithWork_refines [LinearOrder V] [Fintype V] {capacity flow : ArcFlow V}
    (code : V → List Bool) (injective : Function.Injective code) (w : ℕ) (bounded : ∀ v, (code v).length ≤ w)
    (arcs : List (V × V)) (rows : List (BinaryCapacityFlowRow (V × V))) (source : V)
    (capacityWidth flowWidth : ℕ)
    (complete : ∀ e, e ∈ rows.map BinaryCapacityFlowRow.arc)
    (decoded : ∀ row ∈ rows, (binaryWordValue row.capacity : ℤ) = capacity row.arc ∧
      row.flow.value = flow row.arc ∧ row.capacity.length ≤ capacityWidth ∧ row.flow.magnitude.length ≤ flowWidth) :
    let out := binaryFlowCutWithWork (binaryEncodeArcs code arcs) (binaryEncodeCapacityFlowRows code rows)
      (code source) (Fintype.card V)
    ∃ cut : List (V × V), out.1 = binaryEncodeArcs code cut ∧
      cut.toFinset = outgoingCut arcs.toFinset (residualReach capacity flow source) ∧
      (arcs.Nodup → cut.Nodup) ∧
      out.2 ≤ binaryFlowCutWorkBudget (Fintype.card V) arcs.length rows.length w capacityWidth flowWidth (Fintype.card V) := by
  let residual := (rows.map BinaryCapacityFlowRow.arc).filter fun e => decide (flow e < capacity e)
  have sameSet : residual.toFinset = residualArcs capacity flow := by
    ext e
    simp [residual,residualArcs,complete e]
  have size : residual.length ≤ rows.length := by
    simpa [residual] using List.length_filter_le (fun e : V × V => decide (flow e < capacity e)) (rows.map BinaryCapacityFlowRow.arc)
  obtain ⟨resValue,resCost⟩ := binaryResidualRowsWithWork_spec code capacity flow rows capacityWidth flowWidth decoded
  obtain ⟨cut,value,cutSet,simple,cutCost⟩ := binaryResidualCutWithWork_refines code injective w bounded arcs residual source sameSet
  let result := binaryResidualRowsWithWork (binaryEncodeCapacityFlowRows code rows)
  change result.1 = binaryEncodeArcs code residual at resValue
  change result.2 ≤ _ at resCost
  change ∃ cut : List (V × V), (binaryResidualCutWithWork (binaryEncodeArcs code arcs) result.1
    (code source) (Fintype.card V)).1 = binaryEncodeArcs code cut ∧
    cut.toFinset = outgoingCut arcs.toFinset (residualReach capacity flow source) ∧
    (arcs.Nodup → cut.Nodup) ∧
    result.2+(binaryResidualCutWithWork (binaryEncodeArcs code arcs) result.1
      (code source) (Fintype.card V)).2+4 ≤ _
  rw [resValue]
  refine ⟨cut,value,cutSet,simple,?_⟩
  unfold binaryFlowCutWorkBudget
  apply Nat.add_le_add_right (Nat.add_le_add resCost (cutCost.trans ?_)) 4
  unfold binaryResidualCutWorkBudget
  dsimp
  gcongr

end OnlineReachabilityPreservers
