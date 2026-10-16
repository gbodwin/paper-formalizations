import LightEFTSpanners.StoredCandidateRefinement

/-! Original recursion executes the tail first.  The machine's literal record
order therefore corresponds to the reverse original candidate order. The
schedule hypotheses identify stored host/tape inputs at each actual evolving
selected set; they supply neither a vote nor a distance/transition answer. -/
namespace LightEFTSpanners.StoredCandidates

theorem execute_original {n : ℕ} {J : Type*} [DecidableEq J]
    (Q : List (Fin n × Fin n)) (w : Sym2 (Fin n) → ℚ) (hw : ∀ e,0≤w e)
    (t : ℚ) (eligible : Sym2 (Fin n) → Finset J)
    (host : J → Finset (Sym2 (Fin n))) (tape : SampledGreedy.Tape (Fin n) J)
    (h : ℕ) (rs : List (TypedInput n))
    (hr : ValidSchedule Q w t eligible host tape h rs Q) :
    ∃ out : List (Fin n × Fin n),
      execute (StoredEdges.encode Q) (StoredEdges.encode Q) (StoredRecords.encodeWeights w)
        n h (rs.map encode)=StoredEdges.encode out ∧
      StoredSample.edgeSet out=ExecutableVoting.edges (StoredSample.edgeSet Q) w hw t
        eligible host tape h (rs.map fun R => s(R.edge.1,R.edge.2)).reverse := by
  refine ⟨selected Q w h rs Q,execute_encoded Q Q w h rs,?_⟩
  rw [selected_eq_fold Q Q w hw t eligible host tape h rs hr,
    original_edges_eq_fold,List.reverse_reverse]

theorem execute_original_real {n : ℕ} {J : Type*} [DecidableEq J]
    (Q : List (Fin n × Fin n)) (w : Sym2 (Fin n) → ℚ) (hw : ∀ e,0≤w e)
    (t : ℚ) (eligible : Sym2 (Fin n) → Finset J)
    (host : J → Finset (Sym2 (Fin n))) (tape : SampledGreedy.Tape (Fin n) J)
    (h : ℕ) (rs : List (TypedInput n))
    (hr : ValidSchedule Q w t eligible host tape h rs Q) :
    ∃ out : List (Fin n × Fin n),
      execute (StoredEdges.encode Q) (StoredEdges.encode Q) (StoredRecords.encodeWeights w)
        n h (rs.map encode)=StoredEdges.encode out ∧
      StoredSample.edgeSet out=SampledGreedy.edges (StoredSample.edgeSet Q)
        (fun d => (w d:ℝ)) (t:ℝ) eligible host tape h
        (rs.map fun R => s(R.edge.1,R.edge.2)).reverse := by
  simpa only [ExecutableVoting.edges_eq] using
    execute_original Q w hw t eligible host tape h rs hr
end LightEFTSpanners.StoredCandidates
