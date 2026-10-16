import LightEFTSpanners.StoredHostTrace

namespace LightEFTSpanners.StoredHosts
open Controller

def inputBound (n : ℕ) (Q E : List StoredEdges.Edge) (R : Input) : ℕ :=
  StoredVote.bound n Q E R.edges R.draws

def execute (Q E : List StoredEdges.Edge) (W : StoredRecords.Weights)
    (n u v h : ℕ) (budget : ℚ) (rs : List Input) : Bool :=
  match Controller.run (transition Q E W n u v h budget) (bound (inputBound n Q E) rs) (.hosts rs 0) with
  | .halt b => b
  | _ => false

theorem run_encoded {n : ℕ} (Q E : List (Fin n × Fin n)) (w : Sym2 (Fin n) → ℚ)
    (u v : Fin n) (h : ℕ) (budget : ℚ) (rs : List (TypedInput n)) :
    Controller.run (transition (StoredEdges.encode Q) (StoredEdges.encode E) (StoredRecords.encodeWeights w)
      n u.val v.val h budget)
      (bound (inputBound n (StoredEdges.encode Q) (StoredEdges.encode E)) (rs.map encode))
      (.hosts (rs.map encode) 0)=.halt (decide (h≤votes Q E w u v budget rs)) := by
  obtain ⟨k,hk,ht⟩ := hosts_trace Q E w u v h budget rs 0
  simp only [zero_add] at ht
  have hb : k≤bound (inputBound n (StoredEdges.encode Q) (StoredEdges.encode E)) (rs.map encode) := by
    simpa only [bound,List.map_map,Function.comp_def,inputBound,encode,hostBound] using hk
  have he : bound (inputBound n (StoredEdges.encode Q) (StoredEdges.encode E)) (rs.map encode)=
      k+(bound (inputBound n (StoredEdges.encode Q) (StoredEdges.encode E)) (rs.map encode)-k) := by omega
  rw [he,Controller.run_add,ht.run_eq]
  exact Controller.run_terminal _ _ rfl _

theorem execute_encoded {n : ℕ} (Q E : List (Fin n × Fin n)) (w : Sym2 (Fin n) → ℚ)
    (u v : Fin n) (h : ℕ) (budget : ℚ) (rs : List (TypedInput n)) :
    execute (StoredEdges.encode Q) (StoredEdges.encode E) (StoredRecords.encodeWeights w)
      n u.val v.val h budget (rs.map encode)=decide (h≤votes Q E w u v budget rs) := by
  simp only [execute,run_encoded]

theorem decision_iff_estimate {n : ℕ} (Q E : List (Fin n × Fin n)) (w : Sym2 (Fin n) → ℚ)
    (hw : ∀ e,0≤w e) (t : ℚ) (u v : Fin n) (R : TypedInput n) :
    decision Q E w u v (t*w s(u,v)) R=true ↔
      (3:ℚ)/8≤ExecutableVoting.estimate (StoredSample.edgeSet Q) (StoredSample.edgeSet E)
        (StoredSample.edgeSet R.edges) w hw t s(u,v) (R.draws.map StoredSample.edgeSet) := by
  have h := SampleVote.execute_iff_estimate (StoredSample.edgeSet Q) (StoredSample.edgeSet E)
    (StoredSample.edgeSet R.edges) w hw t u v (R.draws.map StoredSample.edgeSet)
  rw [SampleVote.execute_encoded] at h
  simpa only [decision,List.length_map] using h
end LightEFTSpanners.StoredHosts
