import OnlineReachabilityPreservers.SteinerThinBitInitializationWork
import OnlineReachabilityPreservers.SteinerThinBitServiceWork

/-! Stream load increments and rounded demand decisions for a supplied cut trace. -/

namespace OnlineReachabilityPreservers

/-- All values read by one binary cut-and-query step are supplied as bit lists. -/
structure BinaryThinCutQuery where
  cut : List (List Bool × List Bool)
  source : List Bool
  target : List Bool

/-- The load update and demand whose identifiers are used by a trial. -/
abbrev ThinCutQuery (n : ℕ) := List (Fin n × Fin n) × (Fin n × Fin n)

def BinaryThinCutQuery.encode {n : ℕ} (code : Fin n → List Bool) (step : ThinCutQuery n) : BinaryThinCutQuery :=
  ⟨binaryEncodeArcs code step.1,code step.2.1,code step.2.2⟩

/-- Stream the cuts, checking each demand after its cut has updated the
loads. The stored threshold rows and encoded identifiers are reused. -/
def binaryThinCutTraceWithWork {n : ℕ} (base factor : List Bool) (rows : List (BinaryThinThresholdRow n))
    (depth : ℕ) : List BinaryThinCutQuery → List (List Bool) → (List (List Bool) × List Bool) × ℕ
  | [], cells => ((cells,[]),3)
  | step::rest, cells =>
    let updated := bumpBinaryThinCutWithWork base cells step.cut
    let miss := roundBinaryThinServiceWithWork base factor updated.1 rows step.source step.target depth
    let tail := binaryThinCutTraceWithWork base factor rows depth rest updated.1
    ((tail.1.1,miss.1::tail.1.2),updated.2+miss.2+tail.2+8)

/-- The same supplied trace evaluated with the indexed load update and
the word-work miss decision used by the thin replay. -/
def thinCutTraceReference {n : ℕ} (factor : ℕ) (rows : List (BinaryThinThresholdRow n))
    (unique : ((rows.map BinaryThinThresholdRow.reference).map Prod.fst).Nodup) :
    List (ThinCutQuery n) → FinThinLoadTable n → FinThinLoadTable n × List Bool
  | [], table => (table,[])
  | (cut,demand)::rest, table =>
    let updated := (bumpFinThinLoadsWithWordWork table cut).1
    let miss := (roundThinServiceWithWordWork (rows.map BinaryThinThresholdRow.reference) unique
      factor (fun arc => (updated.read arc,0)) n demand).1.2.1
    let tail := thinCutTraceReference factor rows unique rest updated
    (tail.1,miss::tail.2)

/-- Sum the table and trial work over the supplied trace. -/
def binaryThinCutTraceWorkBudget (n rows base labels samples factor payload steps cutCells : ℕ) : ℕ :=
  let update := binaryThinLoadBumpWorkBudget (n*n) base labels payload+5
  let trial := binaryThinServiceWorkBudget n rows base labels samples factor payload n
  3+steps*(11+trial)+cutCells*update

private theorem thinLoadTable_eq_of_read {n : ℕ} {a b : FinThinLoadTable n}
    (same : a.read = b.read) : a = b := by
  apply Subtype.ext
  apply Array.ext (a.property.trans b.property.symm)
  intro i ia ib
  let slot : Fin (n*n) := ⟨i,a.property ▸ ia⟩
  let arc : Fin n × Fin n := finProdFinEquiv.symm slot
  have address : (finProdFinEquiv arc).val = i := congrArg Fin.val (finProdFinEquiv.apply_symm_apply slot)
  have values := congrFun same arc
  change a.val[(finProdFinEquiv arc).val]'(by rw [a.property]; exact (finProdFinEquiv arc).isLt) =
    b.val[(finProdFinEquiv arc).val]'(by rw [b.property]; exact (finProdFinEquiv arc).isLt) at values
  simpa only [address] using values

private theorem encodedCut_match {n labelWidth : ℕ} (code : Fin n → List Bool)
    (numeric : ∀ v, binaryWordValue (code v) = v.val) (bounded : ∀ v, (code v).length ≤ labelWidth)
    (cut : List (Fin n × Fin n)) :
    List.Forall₂ (BinaryThinArcMatches labelWidth) (binaryEncodeArcs code cut) cut := by
  induction cut with
  | nil => exact .nil
  | cons arc rest ih => exact .cons ⟨numeric _,numeric _,bounded _,bounded _⟩ ih

/-- Every step uses exactly the indexed update and word-work miss flag.
A terminal count bound keeps all earlier increments within the payload
width. The trace's cuts, labels, and threshold samples are supplied. -/
theorem binaryThinCutTraceWithWork_spec {n labelWidth sampleWidth loadWidth : ℕ}
    (base factor : List Bool) (rows : List (BinaryThinThresholdRow n))
    (size : binaryWordValue base = n)
    (code : Fin n → List Bool) (numeric : ∀ v, binaryWordValue (code v) = v.val)
    (bounded : ∀ v, (code v).length ≤ labelWidth)
    (labels : ∀ row ∈ rows, row.labels = (code row.arc.1,code row.arc.2))
    (samples : ∀ row ∈ rows, row.sample.length ≤ sampleWidth)
    (uniqueRows : ((rows.map BinaryThinThresholdRow.reference).map Prod.fst).Nodup)
    (steps : List (ThinCutQuery n)) (table : FinThinLoadTable n) (cells : List (List Bool))
    (encoded : EncodesThinLoadTable table cells loadWidth)
    (simple : ∀ step ∈ steps, step.1.Nodup)
    (fits : ∀ arc, table.read arc+(steps.flatMap Prod.fst).count arc < 2^loadWidth) :
    let out := binaryThinCutTraceWithWork base factor rows n (steps.map (BinaryThinCutQuery.encode code)) cells
    let ref := thinCutTraceReference (binaryWordValue factor) rows uniqueRows steps table
    EncodesThinLoadTable ref.1 out.1.1 loadWidth ∧ out.1.2 = ref.2 ∧
      out.2 ≤ binaryThinCutTraceWorkBudget n rows.length base.length labelWidth sampleWidth factor.length loadWidth
        steps.length (steps.flatMap Prod.fst).length := by
  have injective : Function.Injective code := fun _ _ equal =>
    Fin.ext ((numeric _).symm.trans ((congrArg binaryWordValue equal).trans (numeric _)))
  have bounds : ∀ row ∈ rows, BinaryThinArcMatches labelWidth row.labels row.arc ∧ row.sample.length ≤ sampleWidth := by
    intro row present
    refine ⟨?_,samples row present⟩
    rw [labels row present]
    exact ⟨numeric _,numeric _,bounded _,bounded _⟩
  induction steps generalizing table cells with
  | nil => simpa [binaryThinCutTraceWithWork,thinCutTraceReference,binaryThinCutTraceWorkBudget] using encoded
  | cons step rest ih =>
    let cut := step.1
    let demand := step.2
    let updated := bumpBinaryThinCutWithWork base cells (binaryEncodeArcs code cut)
    let next := (bumpFinThinLoadsWithWordWork table cut).1
    have cutSimple : cut.Nodup := simple step List.mem_cons_self
    have splitCount (arc : Fin n × Fin n) :
        ((step::rest).flatMap Prod.fst).count arc = cut.count arc+(rest.flatMap Prod.fst).count arc := by simp [cut]
    have firstFit (arc : Fin n × Fin n) : table.read arc+cut.count arc < 2^loadWidth := by
      have terminal := fits arc
      rw [splitCount] at terminal
      omega
    obtain ⟨⟨nextTable,represented,sameTable⟩,updateCost⟩ := bumpBinaryThinCutWithWork_refines
      table cells base (binaryEncodeArcs code cut) cut encoded size (encodedCut_match code numeric bounded cut) cutSimple firstFit
    have exactTable : nextTable = next := thinLoadTable_eq_of_read sameTable
    rw [exactTable] at represented
    have fitTail (arc : Fin n × Fin n) : next.read arc+(rest.flatMap Prod.fst).count arc < 2^loadWidth := by
      have terminal := fits arc
      rw [splitCount] at terminal
      have value := congrFun (bumpFinThinLoadsWithWordWork_spec table cut cutSimple).1 arc
      change next.read arc = doubleCut cut.toFinset table.read arc at value
      by_cases hit : arc ∈ cut
      · rw [List.count_eq_one_of_mem cutSimple hit] at terminal
        simp only [doubleCut,List.mem_toFinset,hit,↓reduceIte] at value
        rw [value]
        omega
      · rw [List.count_eq_zero_of_not_mem hit] at terminal
        simp only [doubleCut,List.mem_toFinset,hit,↓reduceIte] at value
        rw [value]
        omega
    obtain ⟨miss,queryCost⟩ := roundBinaryThinServiceWithWork_refines next base factor updated.1 rows represented
      size bounds code injective bounded labels uniqueRows demand
    obtain ⟨final,flags,tailCost⟩ := ih next updated.1 represented
      (fun s h => simple s (List.mem_cons_of_mem _ h)) fitTail
    let query := roundBinaryThinServiceWithWork base factor updated.1 rows (code demand.1) (code demand.2) n
    let tail := binaryThinCutTraceWithWork base factor rows n (rest.map (BinaryThinCutQuery.encode code)) updated.1
    let old := thinCutTraceReference (binaryWordValue factor) rows uniqueRows rest next
    let update := binaryThinLoadBumpWorkBudget (n*n) base.length labelWidth loadWidth+5
    let trial := binaryThinServiceWorkBudget n rows.length base.length labelWidth sampleWidth factor.length loadWidth n
    refine ⟨final,?_⟩
    constructor
    · change query.1::tail.1.2 = _::_
      rw [show tail.1.2 = old.2 from flags]
      exact congrArg (fun value => value::old.2) miss
    · rw [List.flatMap_cons,List.length_append]
      change updated.2+query.2+tail.2+8 ≤
        3+(rest.length+1)*(11+trial)+(cut.length+(rest.flatMap Prod.fst).length)*update
      change updated.2 ≤ 3+cut.length*update at updateCost
      have checked : query.2 ≤ trial := queryCost
      change tail.2 ≤ 3+rest.length*(11+trial)+(rest.flatMap Prod.fst).length*update at tailCost
      rw [Nat.add_mul rest.length 1 (11+trial),Nat.one_mul,
        Nat.add_mul cut.length (rest.flatMap Prod.fst).length update]
      omega

/-- Construct the zero table and then evaluate the supplied cut trace. -/
def binaryThinCutTraceFromEmptyWithWork {n : ℕ} (base factor width : List Bool)
    (rows : List (BinaryThinThresholdRow n)) (depth : ℕ) (trace : List BinaryThinCutQuery) :
    (List (List Bool) × List Bool) × ℕ :=
  let initial := emptyBinaryThinLoadsWithWork base width
  let out := binaryThinCutTraceWithWork base factor rows depth trace initial.1
  (out.1,initial.2+out.2+4)

/-- Starting from the constructed zero table, all miss flags and the
ending load cells agree with the reference trace from an empty table. -/
theorem binaryThinCutTraceFromEmptyWithWork_spec {n labelWidth sampleWidth : ℕ}
    (base factor width : List Bool) (rows : List (BinaryThinThresholdRow n))
    (size : binaryWordValue base = n)
    (code : Fin n → List Bool) (numeric : ∀ v, binaryWordValue (code v) = v.val)
    (bounded : ∀ v, (code v).length ≤ labelWidth)
    (labels : ∀ row ∈ rows, row.labels = (code row.arc.1,code row.arc.2))
    (samples : ∀ row ∈ rows, row.sample.length ≤ sampleWidth)
    (uniqueRows : ((rows.map BinaryThinThresholdRow.reference).map Prod.fst).Nodup)
    (steps : List (ThinCutQuery n)) (simple : ∀ step ∈ steps, step.1.Nodup)
    (fits : ∀ arc, (steps.flatMap Prod.fst).count arc < 2^binaryWordValue width) :
    let out := binaryThinCutTraceFromEmptyWithWork base factor width rows n (steps.map (BinaryThinCutQuery.encode code))
    let ref := thinCutTraceReference (binaryWordValue factor) rows uniqueRows steps (emptyFinThinLoads n)
    EncodesThinLoadTable ref.1 out.1.1 (binaryWordValue width) ∧ out.1.2 = ref.2 ∧
      out.2 ≤ emptyBinaryThinLoadWorkBudget n (binaryWordValue width) base.length width.length+
        binaryThinCutTraceWorkBudget n rows.length base.length labelWidth sampleWidth factor.length
          (binaryWordValue width) steps.length (steps.flatMap Prod.fst).length+4 := by
  let initial := emptyBinaryThinLoadsWithWork base width
  obtain ⟨encoded,initCost⟩ := emptyBinaryThinLoadsWithWork_spec base width size
  have firstFits (arc : Fin n × Fin n) :
      (emptyFinThinLoads n).read arc+(steps.flatMap Prod.fst).count arc < 2^binaryWordValue width := by
    simpa [FinThinLoadTable.read,emptyFinThinLoads] using fits arc
  obtain ⟨final,observed,running⟩ := binaryThinCutTraceWithWork_spec base factor rows size code numeric bounded
    labels samples uniqueRows steps (emptyFinThinLoads n) initial.1 encoded simple firstFits
  refine ⟨final,observed,?_⟩
  exact Nat.add_le_add_right (Nat.add_le_add initCost running) 4

end OnlineReachabilityPreservers
