import OnlineReachabilityPreservers.SteinerBinaryClippedPowerWork
import OnlineReachabilityPreservers.SteinerBinaryFlowRunWork
import OnlineReachabilityPreservers.SteinerThinBitLoadWork

/-! Build all supplied thin capacity rows from the same binary load table. -/

namespace OnlineReachabilityPreservers

private def binaryThinCapacityRowWithWork (active : List (List Bool × List Bool))
    (base ceiling : List Bool) (cells : List (List Bool)) (key : List Bool × List Bool) :
    List Bool × ℕ :=
  let enabled := binaryArcMemWithWork key active
  if enabled.1 then
    let fetched := thinLoadAccessWithBinaryWork cells base key.1 key.2 none
    let capacity := binaryClippedPowerTwoWithWork (fetched.1.1.getD []) ceiling
    (capacity.1,enabled.2+fetched.2+capacity.2+8)
  else ([],enabled.2+4)

private def binaryThinCapacityRowWorkBudget (n active base labelWidth loadWidth ceilingWidth : ℕ) : ℕ :=
  2+active*(10*labelWidth+14)+thinLoadAccessBinaryWorkBudget (n*n) base labelWidth labelWidth+
    binaryClippedPowerTwoWorkBudget loadWidth ceilingWidth+8

/-- Intersect the thin capacities with the supplied ceiling. Rows outside
the active arc set receive zero capacity. -/
def clippedThinArcCapacity {n : ℕ} (active : Arcs (Fin n)) (load : CutLoads (Fin n)) (ceiling : ℕ) :
    ArcFlow (Fin n) :=
  fun arc => if arc ∈ active then min ((2 : ℤ)^load arc) (ceiling : ℤ) else 0

private theorem binaryThinCapacityRowWithWork_spec {n labels width : ℕ} (table : FinThinLoadTable n)
    (code : Fin n → List Bool) (numeric : ∀ v, binaryWordValue (code v) = v.val) (bounded : ∀ v, (code v).length ≤ labels)
    (active : List (Fin n × Fin n)) (base ceiling : List Bool) (size : binaryWordValue base = n)
    (cells : List (List Bool)) (encoded : EncodesThinLoadTable table cells width) (key : Fin n × Fin n) :
    let out := binaryThinCapacityRowWithWork (binaryEncodeArcs code active) base ceiling cells (code key.1,code key.2)
    (binaryWordValue out.1 : ℤ) = clippedThinArcCapacity active.toFinset table.read (binaryWordValue ceiling) key ∧
      out.1.length ≤ ceiling.length ∧
      out.2 ≤ binaryThinCapacityRowWorkBudget n active.length base.length labels width ceiling.length := by
  have injective : Function.Injective code := fun a b equal =>
    Fin.ext ((numeric a).symm.trans ((congrArg binaryWordValue equal).trans (numeric b)))
  let enabled := binaryArcMemWithWork (code key.1,code key.2) (binaryEncodeArcs code active)
  obtain ⟨membership,memberCost⟩ := binaryArcMemWithWork_spec code injective labels bounded key active
  change enabled.1 = decide (key ∈ active) at membership
  change enabled.2 ≤ 2+active.length*(10*labels+14) at memberCost
  let fetched := thinLoadAccessWithBinaryWork cells base (code key.1) (code key.2) none
  let capacity := binaryClippedPowerTwoWithWork (fetched.1.1.getD []) ceiling
  let out := if enabled.1 then (capacity.1,enabled.2+fetched.2+capacity.2+8) else ([],enabled.2+4)
  change (binaryWordValue out.1 : ℤ) = _ ∧ out.1.length ≤ ceiling.length ∧ out.2 ≤ _
  unfold out
  rw [membership]
  by_cases present : key ∈ active
  · obtain ⟨⟨cell,inCells,found,value⟩,readCost⟩ := thinLoadAccessWithBinaryWork_read_decoded table cells
      binaryWordValue key base (code key.1) (code key.2) encoded.1 size (numeric key.1) (numeric key.2)
    obtain ⟨amount,length,powCost⟩ := binaryClippedPowerTwoWithWork_spec (fetched.1.1.getD []) ceiling
    change fetched.1.1 = some cell at found
    change binaryWordValue capacity.1 = _ at amount
    change capacity.1.length ≤ ceiling.length at length
    change capacity.2 ≤ _ at powCost
    simp only [found,Option.getD_some,value,encoded.2 cell inCells] at amount powCost
    have readBound := readCost.trans (thinLoadAccessBinaryWorkBudget_le (bounded key.1) (bounded key.2))
    change fetched.2 ≤ _ at readBound
    rw [decide_eq_true present]
    refine ⟨?_,length,?_⟩
    · have cast : (binaryWordValue capacity.1 : ℤ) =
          min ((2 : ℤ)^table.read key) (binaryWordValue ceiling : ℤ) := by exact_mod_cast amount
      simpa [clippedThinArcCapacity,present] using cast
    · exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add memberCost readBound) powCost) _
  · rw [decide_eq_false present]
    refine ⟨by simp [binaryWordValue,clippedThinArcCapacity,present],by simp,?_⟩
    change enabled.2+4 ≤ _
    unfold binaryThinCapacityRowWorkBudget
    omega

/-- Emit one capacity word for each supplied ordered pair, in the original table order. -/
def binaryThinCapacityRowsWithWork (active : List (List Bool × List Bool))
    (base ceiling : List Bool) (cells : List (List Bool)) :
    List (List Bool × List Bool) → List ((List Bool × List Bool) × List Bool) × ℕ
  | [] => ([],2)
  | key::rest =>
    let first := binaryThinCapacityRowWithWork active base ceiling cells key
    let tail := binaryThinCapacityRowsWithWork active base ceiling cells rest
    ((key,first.1)::tail.1,first.2+tail.2+5)

def binaryThinCapacityRowsWorkBudget (n active rows base labels loadWidth ceilingWidth : ℕ) : ℕ :=
  2+rows*(binaryThinCapacityRowWorkBudget n active base labels loadWidth ceilingWidth+5)

/-- The emitted words represent the exact clipped thin capacities, and
each key stays at its supplied position, including if keys repeat. -/
theorem binaryThinCapacityRowsWithWork_spec {n labels width : ℕ} (table : FinThinLoadTable n)
    (code : Fin n → List Bool) (numeric : ∀ v, binaryWordValue (code v) = v.val) (bounded : ∀ v, (code v).length ≤ labels)
    (active keys : List (Fin n × Fin n)) (base ceiling : List Bool) (size : binaryWordValue base = n)
    (cells : List (List Bool)) (encoded : EncodesThinLoadTable table cells width) :
    let out := binaryThinCapacityRowsWithWork (binaryEncodeArcs code active) base ceiling cells (binaryEncodeArcs code keys)
    ∃ rows : List ((Fin n × Fin n) × List Bool), out.1 = binaryEncodeCapacityRows code rows ∧ rows.map Prod.fst = keys ∧
      (∀ row ∈ rows, (binaryWordValue row.2 : ℤ) =
        clippedThinArcCapacity active.toFinset table.read (binaryWordValue ceiling) row.1 ∧ row.2.length ≤ ceiling.length) ∧
      out.2 ≤ binaryThinCapacityRowsWorkBudget n active.length keys.length base.length labels width ceiling.length := by
  induction keys with
  | nil => exact ⟨[],rfl,rfl,by simp,by simp [binaryThinCapacityRowsWithWork,binaryThinCapacityRowsWorkBudget,binaryEncodeArcs]⟩
  | cons key rest ih =>
    let first := binaryThinCapacityRowWithWork (binaryEncodeArcs code active) base ceiling cells (code key.1,code key.2)
    let tail := binaryThinCapacityRowsWithWork (binaryEncodeArcs code active) base ceiling cells (binaryEncodeArcs code rest)
    let perRow := binaryThinCapacityRowWorkBudget n active.length base.length labels width ceiling.length
    obtain ⟨value,length,cost⟩ := binaryThinCapacityRowWithWork_spec table code numeric bounded active base ceiling size
      cells encoded key
    obtain ⟨rows,restValue,restKeys,restDecoded,restCost⟩ := ih
    change tail.1 = _ at restValue
    change first.2 ≤ perRow at cost
    change tail.2 ≤ 2+rest.length*(perRow+5) at restCost
    refine ⟨(key,first.1)::rows,?_,by simp [restKeys],?_,?_⟩
    · change ((code key.1,code key.2),first.1)::tail.1 =
        ((code key.1,code key.2),first.1)::binaryEncodeCapacityRows code rows
      exact congrArg _ restValue
    · intro row onRows
      rcases List.mem_cons.mp onRows with rfl | subset
      · exact ⟨value,length⟩
      · exact restDecoded row subset
    · change first.2+tail.2+5 ≤ 2+(rest.length+1)*(perRow+5)
      rw [Nat.succ_mul rest.length]
      omega

theorem binaryThinCapacityRowsWorkBudget_mono_active (n rows base labels payload ceiling : ℕ) :
    Monotone (fun active => binaryThinCapacityRowsWorkBudget n active rows base labels payload ceiling) := by
  intro smaller larger fits
  change binaryThinCapacityRowsWorkBudget n smaller rows base labels payload ceiling ≤
    binaryThinCapacityRowsWorkBudget n larger rows base labels payload ceiling
  unfold binaryThinCapacityRowsWorkBudget binaryThinCapacityRowWorkBudget
  gcongr

end OnlineReachabilityPreservers
