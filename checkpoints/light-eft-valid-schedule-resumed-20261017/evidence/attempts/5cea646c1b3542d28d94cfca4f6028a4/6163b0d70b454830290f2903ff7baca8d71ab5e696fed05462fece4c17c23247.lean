import LightEFTSpanners.StoredPreparedHostVote

namespace LightEFTSpanners.StoredPreparedHostVote
open StoredHostPreparation (Record TypedRecord)

def execute (Q E : List StoredEdges.Edge) (W : StoredRecords.Weights)
    (n u v h : ℕ) (budget : ℚ) (rs : List Record) : Bool :=
  match Controller.run (transition Q E W n u v h budget) (inputBound n Q E rs)
      (.prepare (.prepare (.records rs []))) with
  | .halt yes => yes
  | _ => false

theorem execute_encoded {n : ℕ} (Q E : List (Fin n × Fin n))
    (w : Sym2 (Fin n) → ℚ) (u v : Fin n) (h : ℕ) (budget : ℚ)
    (rs : List (TypedRecord n)) :
    execute (StoredEdges.encode Q) (StoredEdges.encode E) (StoredRecords.encodeWeights w)
      n u.val v.val h budget (rs.map StoredHostPreparation.encode)=
        decide (h≤StoredHosts.votes Q E w u v budget
          ((rs.filter (StoredHostPreparation.eligible u v)).map TypedRecord.host)) := by
  obtain ⟨k,hk,ht⟩ := prepared_vote_trace Q E w u v h budget rs
  have he : inputBound n (StoredEdges.encode Q) (StoredEdges.encode E) (rs.map StoredHostPreparation.encode)=
      k+(inputBound n (StoredEdges.encode Q) (StoredEdges.encode E) (rs.map StoredHostPreparation.encode)-k) := by omega
  unfold execute
  rw [he,Controller.run_add,ht.run_eq,Controller.run_terminal _ _ rfl]

end LightEFTSpanners.StoredPreparedHostVote
