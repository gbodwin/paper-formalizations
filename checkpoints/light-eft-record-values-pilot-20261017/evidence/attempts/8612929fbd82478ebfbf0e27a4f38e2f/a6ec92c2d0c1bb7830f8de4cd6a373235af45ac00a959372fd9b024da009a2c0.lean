import LightEFTSpanners.StoredVoteTrace

namespace LightEFTSpanners.StoredVote
open Controller

def encodeDraws {n : ℕ} (ss : List (List (Fin n × Fin n))) : Draws := ss.map StoredEdges.encode

theorem records_encoded {n : ℕ} (Q E T : List (Fin n × Fin n))
    (w : Sym2 (Fin n) → ℚ) (ss : List (List (Fin n × Fin n))) :
    records (StoredEdges.encode Q) (StoredEdges.encode E) (StoredEdges.encode T)
      (StoredRecords.encodeWeights w) (encodeDraws ss)=
      SampleVote.encoded (StoredSample.edgeSet Q) (StoredSample.edgeSet E) (StoredSample.edgeSet T)
        w (ss.map StoredSample.edgeSet) := by
  simp only [records,encodeDraws,SampleVote.encoded,List.map_map]
  apply List.map_congr_left
  intro S _
  exact StoredRecords.values_encode Q E T S w

theorem encoded_vote_trace {n : ℕ} (Q E T : List (Fin n × Fin n))
    (w : Sym2 (Fin n) → ℚ) (u v : Fin n) (budget : ℚ) (ss : List (List (Fin n × Fin n))) :
    ∃ k,k≤buildSteps (StoredEdges.encode Q) (StoredEdges.encode E) (StoredEdges.encode T)
        (StoredRecords.encodeWeights w) (encodeDraws ss)+ss.length*(SampleVote.perSample n+1)+4 ∧
      Trace (transition (StoredEdges.encode Q) (StoredEdges.encode E) (StoredEdges.encode T)
        (StoredRecords.encodeWeights w) n u.val v.val budget) k
        (.draws (encodeDraws ss) [])
        (.halt (SampleVote.finish (SampleVote.failures (StoredSample.edgeSet Q) (StoredSample.edgeSet E)
          (StoredSample.edgeSet T) w u v budget (ss.map StoredSample.edgeSet)) ss.length)) := by
  have hc := construct_trace (StoredEdges.encode Q) (StoredEdges.encode E) (StoredEdges.encode T)
    (StoredRecords.encodeWeights w) n u.val v.val budget (encodeDraws ss)
  rw [records_encoded] at hc
  obtain ⟨k,hk,ht⟩ := SampleVote.samples_trace (StoredSample.edgeSet Q) (StoredSample.edgeSet E)
    (StoredSample.edgeSet T) w u v budget (ss.map StoredSample.edgeSet) 0 0
  simp only [zero_add,List.length_map] at ht hk
  have hv := vote_lift (StoredEdges.encode Q) (StoredEdges.encode E) (StoredEdges.encode T)
    (StoredRecords.encodeWeights w) n u.val v.val budget ht
  have hf := Trace.one (show transition (StoredEdges.encode Q) (StoredEdges.encode E) (StoredEdges.encode T)
    (StoredRecords.encodeWeights w) n u.val v.val budget
    (.vote (.halt (SampleVote.finish (SampleVote.failures (StoredSample.edgeSet Q) (StoredSample.edgeSet E)
      (StoredSample.edgeSet T) w u v budget (ss.map StoredSample.edgeSet)) ss.length)))=
    some (.halt (SampleVote.finish (SampleVote.failures (StoredSample.edgeSet Q) (StoredSample.edgeSet E)
      (StoredSample.edgeSet T) w u v budget (ss.map StoredSample.edgeSet)) ss.length)) from rfl)
  refine ⟨_,?_,hc.trans (hv.trans hf)⟩
  simp only [encodeDraws,List.length_map]
  nlinarith
end LightEFTSpanners.StoredVote
