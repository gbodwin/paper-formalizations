import DirectedFlowCutGap.SourcePackingBoundMonotonicity

namespace DirectedFlowCutGap.SourcePacking
open BinaryArithmetic BinaryRational BinaryFractionalRows

theorem table_encode_length (rows : List (Bits × Bits)) :
    (SourceRowTableProgram.encode rows).length=2*SourceRowTableProgram.bits rows+3*rows.length+1 := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    rcases row with ⟨a,b⟩
    simp only [SourceRowTableProgram.encode,SourceRowTableProgram.bits,List.length_cons,
      List.length_append,SelfDelimitedWordProgram.encode_length,ih]
    omega

theorem input_metrics {n : ℕ} (capacity : Row n) (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (ds : List (BinaryFractionalWalkOracle.Pair n)) :
    let N := (encode capacity adjacency ds).length
    n ≤ N ∧ ds.length ≤ N ∧ SourceRowTableProgram.bits (capacityFields capacity) ≤ N ∧
      PackingSourceInput.inputSize (capacityFields capacity) (matrixFields adjacency) (demandFields ds) ≤ N := by
  have hc : (capacityFields capacity).length=n := by simp [capacityFields,IndexedRationalRead.fields]
  have hd : (demandFields ds).length=ds.length := by simp [demandFields]
  dsimp only [encode,PackingSourceInput.encode]
  simp only [List.length_append,table_encode_length,PackingSourceInput.inputSize]
  omega

/-- An original-source-length envelope. Every dependent width and numerical
fuel is instantiated from this one input length. -/
def sourceBound (N : ℕ) : ℕ := 29*N+31+EnumeratedPacking.instructionBound (N+1) (N+1) (N+1)+2

theorem source_bound {n : ℕ} (capacity : Row n) (adjacency : BinaryFractionalWalkOracle.Adjacency n)
    (ds : List (BinaryFractionalWalkOracle.Pair n)) :
    instructionBound capacity adjacency ds ≤ sourceBound (encode capacity adjacency ds).length := by
  obtain ⟨hn,hd,hB,hs⟩ := input_metrics capacity adjacency ds
  have hp := PackingSourceInput.instructions_le (capacityFields capacity) (matrixFields adjacency) (demandFields ds)
  have he := SourcePackingBound.mono_EnumeratedPacking_instructionBound (Nat.le_succ_of_le hd) (Nat.le_succ_of_le hn) (Nat.le_succ_of_le hB)
  simp only [Nat.succ_eq_add_one] at he
  unfold instructionBound sourceBound
  omega

end DirectedFlowCutGap.SourcePacking
