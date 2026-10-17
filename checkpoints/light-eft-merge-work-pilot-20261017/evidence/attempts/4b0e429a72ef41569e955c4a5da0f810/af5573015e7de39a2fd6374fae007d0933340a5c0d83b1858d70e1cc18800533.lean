import LightEFTSpanners.StoredForestCandidateTrace

namespace LightEFTSpanners.StoredForestCandidate

def typedResult {n : ℕ} (fs : List (List (Fin n × Fin n))) (bank : StoredDrawLookup.TypedBank n)
    (e : Fin n × Fin n) (w : Sym2 (Fin n) → ℚ) (t : ℚ) : StoredCandidates.TypedInput n :=
  StoredCandidatePreparation.typedResult w t
    (StoredComponentCandidate.typedPrepared ⟨e,StoredForestInput.typedInputs bank 0 fs⟩)

theorem value_encoded {n : ℕ} (fs : List (List (Fin n × Fin n))) (bank : StoredDrawLookup.TypedBank n)
    (e : Fin n × Fin n) (w : Sym2 (Fin n) → ℚ) (t : ℚ) :
    value fs (StoredDrawLookup.encode bank) (e.1.val,e.2.val) (StoredRecords.encodeWeights w) t=
      StoredCandidates.encode (typedResult fs bank e w t) := by
  unfold value
  have hi := StoredForestInput.attachment_encoded fs bank 0
  change StoredForestInput.value fs (StoredDrawLookup.encode bank)=
    (StoredForestInput.typedInputs bank 0 fs).map StoredComponentRecord.encode at hi
  rw [hi]
  exact StoredComponentCandidate.result_encoded w t ⟨e,StoredForestInput.typedInputs bank 0 fs⟩

theorem execute_encoded {n : ℕ} (fs : List (List (Fin n × Fin n))) (bank : StoredDrawLookup.TypedBank n)
    (e : Fin n × Fin n) (w : Sym2 (Fin n) → ℚ) (t : ℚ) :
    execute n (fs.map StoredEdges.encode) (StoredDrawLookup.encode bank) (e.1.val,e.2.val)
      (StoredRecords.encodeWeights w) t=some (StoredCandidates.encode (typedResult fs bank e w t)) := by
  rw [execute_eq,value_encoded]
end LightEFTSpanners.StoredForestCandidate
