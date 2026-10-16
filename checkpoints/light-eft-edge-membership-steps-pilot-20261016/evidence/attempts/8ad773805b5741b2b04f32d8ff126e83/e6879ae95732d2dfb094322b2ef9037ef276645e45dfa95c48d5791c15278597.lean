import LightEFTSpanners.StoredHostAdmission

namespace LightEFTSpanners.StoredHosts

/-- The sum charges every actual draw and every stored draw-list cell in every
host record, including repetitions.  Arithmetic and list entries are atoms;
evaluating this fuel expression is outside the transition model. -/
def totalBound (n : ℕ) (Q E : List StoredEdges.Edge) (rs : List Input) : ℕ :=
  (rs.map fun R => R.draws.length *
    (n*n*(Q.length+E.length+R.edges.length+11)+4*n+SampleVote.perSample n+5)+
    n*n*StoredVote.drawCells R.draws).sum+6*rs.length+1

theorem bound_eq_total (n : ℕ) (Q E : List StoredEdges.Edge) (rs : List Input) :
    bound (inputBound n Q E) rs=totalBound n Q E rs := by
  induction rs with
  | nil => simp [bound,totalBound]
  | cons R rs ih =>
    simp only [bound,inputBound,StoredVote.bound,List.map_cons,List.sum_cons,
      totalBound,List.length_cons] at *
    omega

theorem run_with_total_bound {n : ℕ} (Q E : List (Fin n × Fin n))
    (w : Sym2 (Fin n) → ℚ) (u v : Fin n) (h : ℕ) (budget : ℚ)
    (rs : List (TypedInput n)) :
    Controller.run (transition (StoredEdges.encode Q) (StoredEdges.encode E)
      (StoredRecords.encodeWeights w) n u.val v.val h budget)
      (totalBound n (StoredEdges.encode Q) (StoredEdges.encode E) (rs.map encode))
      (.hosts (rs.map encode) 0)=.halt (decide (h≤votes Q E w u v budget rs)) := by
  rw [←bound_eq_total]
  exact run_encoded Q E w u v h budget rs
end LightEFTSpanners.StoredHosts
