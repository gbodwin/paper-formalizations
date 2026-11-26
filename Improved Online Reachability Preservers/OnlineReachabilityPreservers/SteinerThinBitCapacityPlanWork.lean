import OnlineReachabilityPreservers.SteinerThinBitCutTraceWork

/-! Reserve the binary thin payload width from a supplied step budget. -/

namespace OnlineReachabilityPreservers

open Finset

/-- Choose the payload width from the length of the step-budget word.
The reserve is set before any cut or query is examined. -/
def plannedBinaryThinCutTraceWithWork {n : ℕ} (base factor plan : List Bool)
    (rows : List (BinaryThinThresholdRow n)) (depth : ℕ) (steps : List BinaryThinCutQuery) :
    (List (List Bool) × List Bool) × ℕ :=
  let width := binaryWordLengthWithWork plan
  let out := binaryThinCutTraceFromEmptyWithWork base factor width.1 rows depth steps
  (out.1,width.2+out.2+4)

/-- Work of reserving the payload width and processing the supplied trace. -/
def plannedBinaryThinCutTraceWorkBudget
    (n rows base labels samples factor planBits steps cutCells : ℕ) : ℕ :=
  (3+planBits*(20*planBits+9))+
    emptyBinaryThinLoadWorkBudget n planBits base planBits+
    binaryThinCutTraceWorkBudget n rows base labels samples factor planBits steps cutCells+8

private theorem thinCutCounts_le_trace_length {n : ℕ} (steps : List (ThinCutQuery n))
    (simple : ∀ step ∈ steps, step.1.Nodup) (arc : Fin n × Fin n) :
    (steps.flatMap Prod.fst).count arc ≤ steps.length := by
  induction steps with
  | nil => simp
  | cons step rest ih =>
    have repeats := ih (fun step included => simple step (List.mem_cons_of_mem _ included))
    have first := simple step List.mem_cons_self
    have one : step.1.count arc ≤ 1 := by
      by_cases present : arc ∈ step.1
      · rw [List.count_eq_one_of_mem first present]
      · rw [List.count_eq_zero_of_not_mem present]
        decide
    rw [List.flatMap_cons,List.count_append,List.length_cons]
    omega

/-- A planned maximum number of steps bounds each terminal load. The
checked run initializes from that word and matches the exact reference,
including on any shorter supplied trace. -/
theorem plannedBinaryThinCutTraceWithWork_spec {n labelWidth sampleWidth : ℕ}
    (base factor plan : List Bool) (rows : List (BinaryThinThresholdRow n))
    (size : binaryWordValue base = n) (code : Fin n → List Bool)
    (numeric : ∀ v, binaryWordValue (code v) = v.val) (bounded : ∀ v, (code v).length ≤ labelWidth)
    (labels : ∀ row ∈ rows, row.labels = (code row.arc.1,code row.arc.2))
    (samples : ∀ row ∈ rows, row.sample.length ≤ sampleWidth)
    (uniqueRows : ((rows.map BinaryThinThresholdRow.reference).map Prod.fst).Nodup)
    (steps : List (ThinCutQuery n)) (simple : ∀ step ∈ steps, step.1.Nodup)
    (fits : steps.length ≤ binaryWordValue plan) :
    let out := plannedBinaryThinCutTraceWithWork base factor plan rows n (steps.map (BinaryThinCutQuery.encode code))
    let ref := thinCutTraceReference (binaryWordValue factor) rows uniqueRows steps (emptyFinThinLoads n)
    EncodesThinLoadTable ref.1 out.1.1 plan.length ∧ out.1.2 = ref.2 ∧
      out.2 ≤ plannedBinaryThinCutTraceWorkBudget n rows.length base.length labelWidth sampleWidth factor.length
        plan.length steps.length (steps.flatMap Prod.fst).length := by
  let width := binaryWordLengthWithWork plan
  let evaluated := binaryThinCutTraceFromEmptyWithWork base factor width.1 rows n
    (steps.map (BinaryThinCutQuery.encode code))
  obtain ⟨value,bits,setup⟩ := binaryWordLengthWithWork_spec plan
  change binaryWordValue width.1 = plan.length at value
  have enough (arc : Fin n × Fin n) : (steps.flatMap Prod.fst).count arc < 2^binaryWordValue width.1 := by
    rw [value]
    exact ((thinCutCounts_le_trace_length steps simple arc).trans fits).trans_lt (binaryWordValue_lt_pow plan)
  obtain ⟨represented,flags,spent⟩ := binaryThinCutTraceFromEmptyWithWork_spec base factor width.1 rows size
    code numeric bounded labels samples uniqueRows steps simple enough
  change EncodesThinLoadTable _ evaluated.1.1 (binaryWordValue width.1) at represented
  rw [value] at represented
  refine ⟨represented,flags,?_⟩
  let widthBudget := 3+plan.length*(20*plan.length+9)
  let allocationBudget := emptyBinaryThinLoadWorkBudget n plan.length base.length plan.length
  let traceBudget := binaryThinCutTraceWorkBudget n rows.length base.length labelWidth sampleWidth factor.length
    plan.length steps.length (steps.flatMap Prod.fst).length
  change evaluated.2 ≤ emptyBinaryThinLoadWorkBudget n (binaryWordValue width.1) base.length width.1.length+
    binaryThinCutTraceWorkBudget n rows.length base.length labelWidth sampleWidth factor.length
      (binaryWordValue width.1) steps.length (steps.flatMap Prod.fst).length+4 at spent
  rw [value] at spent
  have alloc : emptyBinaryThinLoadWorkBudget n plan.length base.length width.1.length ≤ allocationBudget := by
    change width.1.length ≤ plan.length at bits
    unfold allocationBudget emptyBinaryThinLoadWorkBudget
    gcongr
  have body : evaluated.2 ≤ allocationBudget+traceBudget+4 :=
    spent.trans (Nat.add_le_add_right (Nat.add_le_add_right alloc traceBudget) 4)
  change width.2 ≤ widthBudget at setup
  change width.2+evaluated.2+4 ≤ widthBudget+allocationBudget+traceBudget+8
  omega

end OnlineReachabilityPreservers
