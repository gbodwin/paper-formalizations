import LightEFTSpanners.StoredPreparedCandidateExecutable
import LightEFTSpanners.StoredCandidateOriginal

namespace LightEFTSpanners.StoredPreparedCandidates
open StoredCandidatePreparation

/-- The actual bank constructor supplies budgets and eligible host lists. The
remaining schedule premise identifies the original host/draw representations. -/
theorem execute_original {n : ℕ} {J : Type*} [DecidableEq J]
    (Q : List (Fin n × Fin n)) (w : Sym2 (Fin n) → ℚ) (hw : ∀ e,0≤w e)
    (t : ℚ) (eligible : Sym2 (Fin n) → Finset J)
    (host : J → Finset (Sym2 (Fin n))) (tape : SampledGreedy.Tape (Fin n) J)
    (h : ℕ) (rs : List (TypedInput n))
    (hr : StoredCandidates.ValidSchedule Q w t eligible host tape h
      (rs.map (typedResult w t)) Q) :
    ∃ out : List (Fin n × Fin n),
      execute (StoredEdges.encode Q) (StoredEdges.encode Q) (StoredRecords.encodeWeights w)
        n h t (rs.map encode)=StoredEdges.encode out ∧
      StoredSample.edgeSet out=SampledGreedy.edges (StoredSample.edgeSet Q)
        (fun d => (w d:ℝ)) (t:ℝ) eligible host tape h
        (rs.map fun r => s(r.edge.1,r.edge.2)).reverse := by
  obtain ⟨out,he,ho⟩ := StoredCandidates.execute_original_real Q w hw t eligible host tape h
    (rs.map (typedResult w t)) hr
  refine ⟨out,?_,?_⟩
  · rw [execute_encoded]
    rw [StoredCandidates.execute_encoded] at he
    exact he
  · simpa only [List.map_map,Function.comp_def,typedResult] using ho
end LightEFTSpanners.StoredPreparedCandidates
