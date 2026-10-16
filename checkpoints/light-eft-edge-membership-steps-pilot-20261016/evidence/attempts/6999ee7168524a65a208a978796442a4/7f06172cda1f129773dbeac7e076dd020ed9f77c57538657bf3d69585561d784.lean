import LightEFTSpanners.StoredAssignmentSchedule

namespace LightEFTSpanners.StoredCandidates

theorem execute_assignment {n m : ℕ} {J : Type*} [DecidableEq J]
    (Q : List (Fin n × Fin n)) (w : Sym2 (Fin n) → ℚ) (hw : ∀ e,0≤w e) (t : ℚ)
    (eligible : Sym2 (Fin n) → Finset J) (host : J → Finset (Sym2 (Fin n)))
    (a : SampledGreedy.Assignment (Fin n) J m) (h : ℕ)
    (js : Sym2 (Fin n) → List J)
    (input : Sym2 (Fin n) → J → StoredHosts.TypedInput n)
    (es : List (Fin n × Fin n))
    (hj : ∀ e∈es,(js s(e.1,e.2)).Nodup)
    (he : ∀ e∈es,(js s(e.1,e.2)).toFinset=eligible s(e.1,e.2))
    (hh : ∀ e∈es,∀ j∈js s(e.1,e.2),host j=StoredSample.edgeSet (input s(e.1,e.2) j).edges)
    (hd : ∀ e∈es,∀ j∈js s(e.1,e.2),
      ((input s(e.1,e.2) j).draws.map StoredSample.edgeSet)=List.ofFn (a s(e.1,e.2) j)) :
    ∃ out : List (Fin n × Fin n),
      execute (StoredEdges.encode Q) (StoredEdges.encode Q) (StoredRecords.encodeWeights w)
        n h ((assignmentRecords w t js input es).map encode)=StoredEdges.encode out ∧
      StoredSample.edgeSet out=SampledGreedy.edges (StoredSample.edgeSet Q)
        (fun d => (w d:ℝ)) (t:ℝ) eligible host (SampledGreedy.assignmentTape a) h
        (es.map fun e => s(e.1,e.2)).reverse := by
  have hs := assignment_schedule Q Q w t eligible host a h js input es hj he hh hd
  simpa only [assignmentRecords,List.map_map,Function.comp_def] using
    execute_original_real Q w hw t eligible host (SampledGreedy.assignmentTape a) h
      (assignmentRecords w t js input es) hs
end LightEFTSpanners.StoredCandidates
