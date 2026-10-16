import LightEFTSpanners.StoredGraphMatrix

namespace LightEFTSpanners.StoredGraphMatrix

theorem values_cellCount (es : StoredSample.EdgeLists) (i : ℕ) (W : StoredRecords.Weights) :
    SampleRecords.cellCount (StoredRecords.values es i W)=StoredRecords.cellCount W := by
  induction W generalizing i with
  | nil => rfl
  | cons row rows ih =>
    simpa [StoredRecords.values,SampleRecords.cellCount,StoredRecords.cellCount] using
      congrArg (row.length+·) (ih (i+1))

def bound (n m : ℕ) : ℕ := n*n*(m+13)+10*n+9

theorem steps_le (n : ℕ) (edges : List StoredEdges.Edge) : steps n edges≤bound n edges.length := by
  have h := StoredRecords.matrixSteps_le (lists edges) (StoredZeroWeights.matrix n)
  have hw : StoredRecords.cellCount (StoredZeroWeights.matrix n)=n*n := by
    simp [StoredRecords.cellCount,StoredZeroWeights.matrix]
  have hl : (StoredZeroWeights.matrix n).length=n := by simp [StoredZeroWeights.matrix]
  rw [hw,hl] at h
  simp only [StoredRecords.listSize,lists,List.length_nil,Nat.zero_add,Nat.add_zero] at h
  unfold steps bound
  rw [values_cellCount,hw]
  have he : n*n*(edges.length+13)=n*n*(edges.length+11)+2*(n*n) := by ring
  rw [he]
  simp only [lists]
  omega

theorem value_encoded {n : ℕ} (edges : List (Fin n × Fin n)) :
    value n (StoredEdges.encode edges)=
      LinkedDistance.matrixOf (ExecutableVoting.graph (StoredSample.edgeSet edges)) (fun _ => 0) := by
  unfold value
  rw [StoredZeroWeights.matrix_encode]
  change SampleRecords.values 0
    (StoredRecords.values (StoredSample.encodeLists [] [] edges []) 0
      (StoredRecords.encodeWeights (fun _ => 0)))=_
  rw [StoredRecords.values_encode,SampleRecords.encode_values]
  simp [ExecutableVoting.sampled,StoredSample.edgeSet]
  rfl
end LightEFTSpanners.StoredGraphMatrix
