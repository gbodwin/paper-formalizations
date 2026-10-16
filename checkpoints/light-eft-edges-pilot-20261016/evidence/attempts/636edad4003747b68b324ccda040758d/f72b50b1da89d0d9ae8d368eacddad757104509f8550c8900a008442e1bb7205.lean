import LightEFTSpanners.StoredHostBound

namespace LightEFTSpanners.StoredHosts

/-- Exact real-weight semantics for this same rational-input execution. -/
theorem execute_iff_real_admission {n : ℕ} {J : Type*} [DecidableEq J]
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
      h≤(SampledGreedy.votes (StoredSample.edgeSet Q) (fun d => (w d:ℝ)) (t:ℝ)
        eligible host tape (StoredSample.edgeSet E) s(u,v)).card := by
  rw [execute_iff_original_admission Q E w hw t u v h eligible host tape js input hj he hh hd,
    ExecutableVoting.votes_eq]
end LightEFTSpanners.StoredHosts
