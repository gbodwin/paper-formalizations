import LightEFTSpanners.StoredHostCount

/-! Refinement for a literal representation of the distinct eligible hosts.
The machine receives only records; these hypotheses identify those records
with the original host/tape data at the current selected set and candidate.
Eligibility construction and raw random-tape generation are not asserted. -/
namespace LightEFTSpanners.StoredHosts

theorem votes_eq_original {n : ℕ} {J : Type*} [DecidableEq J]
    (Q E : List (Fin n × Fin n)) (w : Sym2 (Fin n) → ℚ) (hw : ∀ e,0≤w e)
    (t : ℚ) (u v : Fin n) (eligible : Sym2 (Fin n) → Finset J)
    (host : J → Finset (Sym2 (Fin n))) (tape : SampledGreedy.Tape (Fin n) J)
    (js : List J) (input : J → TypedInput n) (hj : js.Nodup)
    (he : js.toFinset=eligible s(u,v))
    (hh : ∀ j∈js,host j=StoredSample.edgeSet (input j).edges)
    (hd : ∀ j∈js,tape (StoredSample.edgeSet E) s(u,v) j=
      ((input j).draws.map StoredSample.edgeSet)) :
    votes Q E w u v (t*w s(u,v)) (js.map input)=
      (ExecutableVoting.votes (StoredSample.edgeSet Q) w hw t eligible host tape
        (StoredSample.edgeSet E) s(u,v)).card := by
  rw [votes_indexed Q E w u v (t*w s(u,v)) js input hj]
  unfold ExecutableVoting.votes
  rw [←he]
  congr 1
  apply Finset.filter_congr
  intro j hm
  have hm' : j∈js := List.mem_toFinset.mp hm
  rw [decision_iff_estimate Q E w hw t u v,hh j hm',hd j hm']

theorem execute_iff_original_admission {n : ℕ} {J : Type*} [DecidableEq J]
    (Q E : List (Fin n × Fin n)) (w : Sym2 (Fin n) → ℚ) (hw : ∀ e,0≤w e)
    (t : ℚ) (u v : Fin n) (h : ℕ) (eligible : Sym2 (Fin n) → Finset J)
    (host : J → Finset (Sym2 (Fin n))) (tape : SampledGreedy.Tape (Fin n) J)
    (js : List J) (input : J → TypedInput n) (hj : js.Nodup)
    (he : js.toFinset=eligible s(u,v))
    (hh : ∀ j∈js,host j=StoredSample.edgeSet (input j).edges)
    (hd : ∀ j∈js,tape (StoredSample.edgeSet E) s(u,v) j=
      ((input j).draws.map StoredSample.edgeSet)) :
    execute (StoredEdges.encode Q) (StoredEdges.encode E) (StoredRecords.encodeWeights w)
      n u.val v.val h (t*w s(u,v)) ((js.map input).map encode)=true ↔
      h≤(ExecutableVoting.votes (StoredSample.edgeSet Q) w hw t eligible host tape
        (StoredSample.edgeSet E) s(u,v)).card := by
  rw [execute_encoded,decide_eq_true_eq,votes_eq_original Q E w hw t u v eligible host tape js input hj he hh hd]
end LightEFTSpanners.StoredHosts
