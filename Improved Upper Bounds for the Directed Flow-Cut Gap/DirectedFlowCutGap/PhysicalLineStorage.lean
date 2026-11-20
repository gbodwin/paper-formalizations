import DirectedFlowCutGap.BinaryArrayNestedStorage
import DirectedFlowCutGap.PhysicalBinaryEdgeWire

/-! Follow the arrays reached by the price decoder and the original line
preparation before the fractional controller begins. -/
namespace DirectedFlowCutGap.PhysicalLineStorage

open EncodedEdgeLineInput EncodedArrayStorage
open BinaryArrayNestedStorage (Code Grid WithChildren copyBudget cellBudget)
open BinaryArrayBatch (StorageModel)

theorem decode_arrays {n : ℕ} (D : EncodedEdgeInput.Input n) :
    ∃ code, Grid (PhysicalBinaryEdgeWire.decodeWithCost D).1.costs code ∧
      code.length≤(n+1)*copyBudget n ∧ fresh code≤(n+1)*cellBudget n := by
  have h : ∃ code, Grid (PhysicalBinaryEdgeWire.decodeWithCost D).1.costs code ∧
      code.length≤copyBudget n+n*copyBudget n ∧ fresh code≤cellBudget n+n*cellBudget n := by
    unfold PhysicalBinaryEdgeWire.decodeWithCost PhysicalBinaryEdgeWire.decodeWithControl BinaryEdgeProjection.matrixWithControl
    apply BinaryArrayNestedStorage.grid
    intro i
    apply BinaryArrayBatch.runWithChildWork_storage
  simpa only [Nat.add_mul,Nat.one_mul,Nat.add_comm (n*copyBudget n),Nat.add_comm (n*cellBudget n)] using h

def LineArrays {n : ℕ} (D : Input n) (code : Code) : Prop :=
  ∃ labels matrix prices encoded : Code,
    WithChildren (BinaryLineLabels.labels n).1 (fun _ => []) labels ∧
    Grid (BinaryLineLabels.prepare D).1.adjacency matrix ∧
    WithChildren (BinaryLineLabels.prepare D).1.costs (fun _ => []) prices ∧
    WithChildren (PhysicalAmplifiedBinaryEdge.lineWithCost D).1.costs (fun _ => []) encoded ∧
    code=labels++matrix++prices++encoded

theorem line_arrays {n : ℕ} (D : Input n) :
    let m := lineSize n
    ∃ code, LineArrays D code ∧ code.length≤(m+4)*copyBudget m ∧ fresh code≤(m+4)*cellBudget m := by
  let m := lineSize n
  obtain ⟨labels,rows,_,costs⟩ := BinaryLineLabels.prepare_arrays D
  obtain ⟨labelCode,labelRun,labelLength,labelSpace⟩ := BinaryArrayNestedStorage.alone labels
  obtain ⟨priceCode,priceRun,priceLength,priceSpace⟩ := BinaryArrayNestedStorage.alone costs
  have matrix : ∃ code, Grid (BinaryLineLabels.prepare D).1.adjacency code ∧
      code.length≤copyBudget m+m*copyBudget m ∧ fresh code≤cellBudget m+m*cellBudget m := by
    apply BinaryArrayNestedStorage.grid
    exact rows
  obtain ⟨matrixCode,matrixRun,matrixLength,matrixSpace⟩ := matrix
  simp only [m] at matrixLength matrixSpace
  have encoded : StorageModel (PhysicalAmplifiedBinaryEdge.lineWithCost D).1.costs := by
    unfold PhysicalAmplifiedBinaryEdge.lineWithCost PhysicalAmplifiedBinaryEdge.lineWithControl
    apply BinaryArrayBatch.runWithChildWork_storage
  obtain ⟨encodedCode,encodedRun,encodedLength,encodedSpace⟩ := BinaryArrayNestedStorage.alone encoded
  refine ⟨labelCode++matrixCode++priceCode++encodedCode,
    ⟨labelCode,matrixCode,priceCode,encodedCode,labelRun,matrixRun,priceRun,encodedRun,rfl⟩,?_,?_⟩
  · simp only [List.length_append,Nat.add_mul]
    omega
  · simp only [fresh_append,Nat.add_mul]
    omega

def lineSchedule (n : ℕ) : Code :=
  let m := lineSize n
  let flat := BinaryArrayNestedStorage.schedule m (fun _ => [])
  flat++BinaryArrayNestedStorage.gridSchedule m m++flat++flat

theorem line_schedule_eq {n : ℕ} {D : Input n} {code : Code} (run : LineArrays D code) :
    code=lineSchedule n := by
  obtain ⟨labels,matrix,prices,encoded,labelRun,matrixRun,priceRun,encodedRun,rfl⟩ := run
  rw [BinaryArrayNestedStorage.schedule_eq labelRun,BinaryArrayNestedStorage.grid_schedule_eq matrixRun,
    BinaryArrayNestedStorage.schedule_eq priceRun,BinaryArrayNestedStorage.schedule_eq encodedRun]
  rfl

theorem line_schedule {n : ℕ} (D : Input n) : LineArrays D (lineSchedule n) := by
  obtain ⟨_,run,_,_⟩ := line_arrays D
  exact line_schedule_eq run ▸ run

theorem decode_schedule {n : ℕ} (D : EncodedEdgeInput.Input n) :
    Grid (PhysicalBinaryEdgeWire.decodeWithCost D).1.costs (BinaryArrayNestedStorage.gridSchedule n n) := by
  obtain ⟨_,run,_,_⟩ := decode_arrays D
  exact BinaryArrayNestedStorage.grid_schedule_eq run ▸ run

end DirectedFlowCutGap.PhysicalLineStorage
