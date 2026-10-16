import LightEFTSpanners.StoredOriginalWeightRepresentation

namespace LightEFTSpanners.StoredWeightedForestCandidates

theorem execute_original_weights {n : ℕ} (h : ℕ) (fs : List (List (Fin n × Fin n)))
    (Q E : List (Fin n × Fin n)) (w : Sym2 (Fin n) → ℚ) (t : ℚ)
    (rs : List (StoredForestBank.TypedInput n)) :
    execute n h (fs.map StoredEdges.encode) (StoredEdges.encode Q) (StoredEdges.encode E)
      (StoredOriginalWeightLookup.encode (StoredOriginalWeightLookup.originalBank w)) t
      (rs.map StoredForestBank.encode)=
    StoredForestCandidates.execute n h (fs.map StoredEdges.encode) (StoredEdges.encode Q)
      (StoredEdges.encode E) (StoredRecords.encodeWeights w) t (rs.map StoredForestBank.encode) := by
  rw [execute_encoded,StoredForestCandidates.execute_encoded,StoredOriginalWeightLookup.originalBank_represents]

end LightEFTSpanners.StoredWeightedForestCandidates
