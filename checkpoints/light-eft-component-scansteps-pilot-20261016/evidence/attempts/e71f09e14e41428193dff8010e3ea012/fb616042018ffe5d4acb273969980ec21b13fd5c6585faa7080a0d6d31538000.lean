import LightEFTSpanners.StoredCandidateBound

namespace LightEFTSpanners.StoredCandidates

def inputHostCap (n q m : ℕ) (H : StoredHosts.Input) : ℕ :=
  H.draws.length*(n*n*(q+m+H.edges.length+11)+4*n+SampleVote.perSample n+5)+
    n*n*StoredVote.drawCells H.draws+4

def inputCandidateCap (n q m : ℕ) (R : Input) : ℕ :=
  (R.hosts.map fun H => inputHostCap n q m H+2).sum+3

def inputBound (n : ℕ) (Q E : List StoredEdges.Edge) (rs : List Input) : ℕ :=
  (rs.map (inputCandidateCap n Q.length (E.length+rs.length))).sum+1

def execute (Q E : List StoredEdges.Edge) (W : StoredRecords.Weights)
    (n h : ℕ) (rs : List Input) : List StoredEdges.Edge :=
  match Controller.run (transition Q W n h) (inputBound n Q E rs) (.candidates rs E) with
  | .halt out => out
  | _ => E

theorem candidateCap_encoded {n : ℕ} (q m : ℕ) (R : TypedInput n) :
    inputCandidateCap n q m (encode R)=candidateCap q m R := by
  simp only [inputCandidateCap,inputHostCap,candidateCap,hostCap,encode,
    StoredHosts.encode,StoredEdges.encode,StoredVote.encodeDraws,StoredVote.drawCells,
    List.map_map,Function.comp_def,List.length_map]

theorem bound_encoded {n : ℕ} (Q E : List (Fin n × Fin n)) (rs : List (TypedInput n)) :
    inputBound n (StoredEdges.encode Q) (StoredEdges.encode E) (rs.map encode)=
      (rs.map (candidateCap Q.length (E.length+rs.length))).sum+1 := by
  simp only [inputBound,StoredEdges.encode,List.length_map,List.map_map,
    Function.comp_def,candidateCap_encoded]

theorem run_encoded {n : ℕ} (Q E : List (Fin n × Fin n))
    (w : Sym2 (Fin n) → ℚ) (h : ℕ) (rs : List (TypedInput n)) :
    Controller.run (transition (StoredEdges.encode Q) (StoredRecords.encodeWeights w) n h)
      (inputBound n (StoredEdges.encode Q) (StoredEdges.encode E) (rs.map encode))
      (.candidates (rs.map encode) (StoredEdges.encode E))=
      .halt (StoredEdges.encode (selected Q w h rs E)) := by
  obtain ⟨k,hk,ht⟩ := candidates_trace Q E w h rs
  have hb := work_le_input Q E w h (E.length+rs.length) rs (Nat.le_refl _)
  rw [←bound_encoded Q E rs] at hb
  have he : inputBound n (StoredEdges.encode Q) (StoredEdges.encode E) (rs.map encode)=
      k+(inputBound n (StoredEdges.encode Q) (StoredEdges.encode E) (rs.map encode)-k) := by omega
  rw [he,Controller.run_add,ht.run_eq]
  exact Controller.run_terminal _ _ rfl _

theorem execute_encoded {n : ℕ} (Q E : List (Fin n × Fin n))
    (w : Sym2 (Fin n) → ℚ) (h : ℕ) (rs : List (TypedInput n)) :
    execute (StoredEdges.encode Q) (StoredEdges.encode E) (StoredRecords.encodeWeights w)
      n h (rs.map encode)=StoredEdges.encode (selected Q w h rs E) := by
  simp only [execute,run_encoded]
end LightEFTSpanners.StoredCandidates
