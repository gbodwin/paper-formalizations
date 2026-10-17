import LightEFTSpanners.StoredComponentCandidateTotalBound

namespace LightEFTSpanners.StoredComponentCandidates
open StoredComponentCandidate

def execute (Q E : List StoredEdges.Edge) (W : StoredRecords.Weights)
    (n h : ℕ) (t : ℚ) (rs : List Input) : List StoredEdges.Edge :=
  match Controller.run (transition Q E W n h t) (inputBound n Q E rs) (.prepare (.inputs rs [])) with
  | .select (.halt out) => out
  | _ => E

theorem run_encoded {n : ℕ} (Q E : List (Fin n × Fin n))
    (w : Sym2 (Fin n) → ℚ) (h : ℕ) (t : ℚ) (rs : List (TypedInput n)) :
    Controller.run (transition (StoredEdges.encode Q) (StoredEdges.encode E)
      (StoredRecords.encodeWeights w) n h t)
      (inputBound n (StoredEdges.encode Q) (StoredEdges.encode E) (rs.map encode))
      (.prepare (.inputs (rs.map encode) []))=
      .select (.halt (StoredEdges.encode (StoredCandidates.selected Q w h
        (rs.map (fun r => StoredCandidatePreparation.typedResult w t (typedPrepared r))) E))) := by
  obtain ⟨k,hk,ht⟩ := bounded_trace Q E w h t rs
  have he : inputBound n (StoredEdges.encode Q) (StoredEdges.encode E) (rs.map encode)=
      k+(inputBound n (StoredEdges.encode Q) (StoredEdges.encode E) (rs.map encode)-k) := by omega
  rw [he,Controller.run_add,ht.run_eq]
  exact Controller.run_terminal _ _ rfl _

theorem execute_encoded {n : ℕ} (Q E : List (Fin n × Fin n))
    (w : Sym2 (Fin n) → ℚ) (h : ℕ) (t : ℚ) (rs : List (TypedInput n)) :
    execute (StoredEdges.encode Q) (StoredEdges.encode E) (StoredRecords.encodeWeights w)
      n h t (rs.map encode)=StoredEdges.encode (StoredCandidates.selected Q w h
        (rs.map (fun r => StoredCandidatePreparation.typedResult w t (typedPrepared r))) E) := by
  simp only [execute,run_encoded]
end LightEFTSpanners.StoredComponentCandidates
