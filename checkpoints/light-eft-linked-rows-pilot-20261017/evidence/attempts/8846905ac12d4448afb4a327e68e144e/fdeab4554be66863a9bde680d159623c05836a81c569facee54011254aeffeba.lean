import LightEFTSpanners.StoredVoteBound

/-! The actual stored-draw controller returns the inherited empirical vote.
Its fuel is an external expression; no bit cost for that expression is asserted. -/
namespace LightEFTSpanners.StoredVote
open Controller

def execute (Q E T : List StoredEdges.Edge) (W : StoredRecords.Weights)
    (n u v : ℕ) (budget : ℚ) (ss : Draws) : Bool :=
  match Controller.run (transition Q E T W n u v budget) (bound n Q E T ss) (.draws ss []) with
  | .halt b => b
  | _ => false

theorem run_encoded {n : ℕ} (Q E T : List (Fin n × Fin n))
    (w : Sym2 (Fin n) → ℚ) (u v : Fin n) (budget : ℚ) (ss : List (List (Fin n × Fin n))) :
    Controller.run (transition (StoredEdges.encode Q) (StoredEdges.encode E) (StoredEdges.encode T)
      (StoredRecords.encodeWeights w) n u.val v.val budget)
      (bound n (StoredEdges.encode Q) (StoredEdges.encode E) (StoredEdges.encode T) (encodeDraws ss))
      (.draws (encodeDraws ss) [])=
      .halt (SampleVote.finish (SampleVote.failures (StoredSample.edgeSet Q) (StoredSample.edgeSet E)
        (StoredSample.edgeSet T) w u v budget (ss.map StoredSample.edgeSet)) ss.length) := by
  obtain ⟨k,hk,ht⟩ := encoded_vote_trace Q E T w u v budget ss
  have hb := encoded_bound Q E T w ss
  have he : bound n (StoredEdges.encode Q) (StoredEdges.encode E) (StoredEdges.encode T) (encodeDraws ss)=
      k+(bound n (StoredEdges.encode Q) (StoredEdges.encode E) (StoredEdges.encode T) (encodeDraws ss)-k) := by omega
  rw [he,Controller.run_add,ht.run_eq]
  exact Controller.run_terminal _ _ rfl _

theorem execute_iff_estimate {n : ℕ} (Q E T : List (Fin n × Fin n))
    (w : Sym2 (Fin n) → ℚ) (hw : ∀ e,0≤w e) (t : ℚ) (u v : Fin n)
    (ss : List (List (Fin n × Fin n))) :
    execute (StoredEdges.encode Q) (StoredEdges.encode E) (StoredEdges.encode T)
      (StoredRecords.encodeWeights w) n u.val v.val (t*w s(u,v)) (encodeDraws ss)=true ↔
      (3:ℚ)/8≤ExecutableVoting.estimate (StoredSample.edgeSet Q) (StoredSample.edgeSet E)
        (StoredSample.edgeSet T) w hw t s(u,v) (ss.map StoredSample.edgeSet) := by
  have h := SampleVote.execute_iff_estimate (StoredSample.edgeSet Q) (StoredSample.edgeSet E)
    (StoredSample.edgeSet T) w hw t u v (ss.map StoredSample.edgeSet)
  rw [SampleVote.execute_encoded] at h
  simpa only [execute,run_encoded,List.length_map] using h
end LightEFTSpanners.StoredVote
