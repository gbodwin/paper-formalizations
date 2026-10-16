import LightEFTSpanners.StoredRecordTrace

namespace LightEFTSpanners.StoredRecords

def encodeWeights {n : ℕ} (w : Sym2 (Fin n) → ℚ) : Weights :=
  List.ofFn fun u : Fin n => List.ofFn fun v : Fin n => w s(u,v)

theorem rowValues_ofFn (es : StoredSample.EdgeLists) {n : ℕ} (i j : ℕ) (f : Fin n → ℚ) :
    rowValues es i j (List.ofFn f)=List.ofFn (fun v => StoredSample.entry (i,j+v.val) (f v) es) := by
  induction n generalizing j with
  | zero => simp [rowValues]
  | succ n ih =>
    simp only [List.ofFn_succ,rowValues,ih]
    congr 2
    funext v
    congr 1
    simp [Nat.add_comm,Nat.add_left_comm]

theorem values_ofFn (es : StoredSample.EdgeLists) {n : ℕ} (i : ℕ) (f : Fin n → List ℚ) :
    values es i (List.ofFn f)=List.ofFn (fun u => rowValues es (i+u.val) 0 (f u)) := by
  induction n generalizing i with
  | zero => simp [values]
  | succ n ih =>
    simp only [List.ofFn_succ,values,ih]
    congr 2
    funext u
    congr 1
    simp [Nat.add_comm,Nat.add_left_comm]

theorem values_encode {n : ℕ} (Q E T S : List (Fin n × Fin n)) (w : Sym2 (Fin n) → ℚ) :
    values (StoredSample.encodeLists Q E T S) 0 (encodeWeights w)=
      SampleRecords.encode (StoredSample.edgeSet Q) (StoredSample.edgeSet E)
        (StoredSample.edgeSet T) (StoredSample.edgeSet S) w := by
  simp only [encodeWeights,values_ofFn,rowValues_ofFn,zero_add,StoredSample.entry_encoded,SampleRecords.encode]

theorem encoded_steps_le {n : ℕ} (Q E T S : List (Fin n × Fin n)) (w : Sym2 (Fin n) → ℚ) :
    matrixSteps (StoredSample.encodeLists Q E T S) (encodeWeights w) ≤
      n*n*(Q.length+E.length+T.length+S.length+11)+4*n+2 := by
  have h := matrixSteps_le (StoredSample.encodeLists Q E T S) (encodeWeights w)
  simpa [cellCount,listSize,StoredSample.encodeLists,StoredEdges.encode,encodeWeights,
    List.map_ofFn,Function.comp_def] using h

theorem construct_encoded {n : ℕ} (Q E T S : List (Fin n × Fin n)) (w : Sym2 (Fin n) → ℚ) :
    ∃ k,k≤n*n*(Q.length+E.length+T.length+S.length+11)+4*n+2 ∧
      Controller.Trace (transition (StoredSample.encodeLists Q E T S)) k
        (.row 0 (encodeWeights w) [])
        (.halt (SampleRecords.encode (StoredSample.edgeSet Q) (StoredSample.edgeSet E)
          (StoredSample.edgeSet T) (StoredSample.edgeSet S) w)) := by
  exact ⟨_,encoded_steps_le Q E T S w,by simpa only [values_encode] using
      (materialize_trace (StoredSample.encodeLists Q E T S) (encodeWeights w))⟩
end LightEFTSpanners.StoredRecords
