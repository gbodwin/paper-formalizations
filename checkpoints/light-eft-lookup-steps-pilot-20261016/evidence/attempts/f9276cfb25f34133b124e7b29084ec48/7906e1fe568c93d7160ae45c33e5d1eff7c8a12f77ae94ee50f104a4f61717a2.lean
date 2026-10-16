import LightEFTSpanners.StoredComponentCandidate

namespace LightEFTSpanners.StoredComponentCandidate

def inputBound (r : Input) : ℕ :=
  StoredComponentCatalogue.inputBound r.components+r.edge.1+r.edge.2+
    (r.components.map fun x => x.vertices.length*x.vertices.length+3).sum+3*r.components.length+10

theorem prepared_bound (r : Input) :
    StoredCandidatePreparation.inputBound (prepared r)=r.edge.1+r.edge.2+
      (r.components.map fun x => x.vertices.length*x.vertices.length+3).sum+3*r.components.length+9 := by
  simp [StoredCandidatePreparation.inputBound,prepared,StoredPreparedHostRecords.inputBound,
    StoredHostPreparation.inputBound,StoredComponentCatalogue.result,StoredComponentRecord.result,
    List.map_map,Function.comp_def]
  omega

theorem steps_le_input (W : StoredRecords.Weights) (r : Input) : steps W r ≤ inputBound r := by
  have hc := StoredComponentCatalogue.steps_le_input r.components
  have hp := StoredCandidatePreparation.steps_le W (prepared r)
  rw [prepared_bound] at hp
  unfold steps inputBound
  omega

structure TypedInput (n : ℕ) where
  edge : Fin n × Fin n
  components : List (StoredComponentRecord.TypedInput n)

def encode {n : ℕ} (r : TypedInput n) : Input :=
  ⟨(r.edge.1.val,r.edge.2.val),r.components.map StoredComponentRecord.encode⟩
def typedPrepared {n : ℕ} (r : TypedInput n) : StoredCandidatePreparation.TypedInput n :=
  ⟨r.edge,r.components.map StoredComponentRecord.typedResult⟩

theorem prepared_encoded {n : ℕ} (r : TypedInput n) :
    prepared (encode r)=StoredCandidatePreparation.encode (typedPrepared r) := by
  simp only [prepared,encode,typedPrepared,StoredCandidatePreparation.encode,StoredComponentCatalogue.result_encoded]

theorem result_encoded {n : ℕ} (w : Sym2 (Fin n) → ℚ) (t : ℚ) (r : TypedInput n) :
    result (StoredRecords.encodeWeights w) t (encode r)=
      StoredCandidates.encode (StoredCandidatePreparation.typedResult w t (typedPrepared r)) := by
  rw [result,prepared_encoded,StoredCandidatePreparation.result_encoded]
end LightEFTSpanners.StoredComponentCandidate
