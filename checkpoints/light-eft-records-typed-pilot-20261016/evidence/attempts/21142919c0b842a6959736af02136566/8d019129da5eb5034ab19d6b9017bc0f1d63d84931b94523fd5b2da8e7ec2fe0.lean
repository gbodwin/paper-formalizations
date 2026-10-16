import LightEFTSpanners.StoredCandidateTrace

namespace LightEFTSpanners.StoredCandidates

def hostCap {n : ℕ} (q m : ℕ) (H : StoredHosts.TypedInput n) : ℕ :=
  H.draws.length*(n*n*(q+m+H.edges.length+11)+4*n+SampleVote.perSample n+5)+
    n*n*(H.draws.map List.length).sum+4

def candidateCap {n : ℕ} (q m : ℕ) (R : TypedInput n) : ℕ :=
  (R.hosts.map fun H => hostCap q m H+2).sum+3

theorem hostBound_le {n : ℕ} (Q E : List (Fin n × Fin n))
    (H : StoredHosts.TypedInput n) (m : ℕ) (hm : E.length≤m) :
    StoredHosts.hostBound Q E H≤hostCap Q.length m H := by
  simp only [StoredHosts.hostBound,StoredVote.bound,StoredEdges.encode,
    StoredVote.encodeDraws,StoredVote.drawCells,List.length_map,List.map_map,
    Function.comp_def,hostCap]
  gcongr

theorem hostSum_le {n : ℕ} (Q E : List (Fin n × Fin n))
    (hs : List (StoredHosts.TypedInput n)) (m : ℕ) (hm : E.length≤m) :
    (hs.map fun H => StoredHosts.hostBound Q E H+2).sum≤
      (hs.map fun H => hostCap Q.length m H+2).sum := by
  induction hs with
  | nil => exact Nat.le_refl 0
  | cons H hs ih =>
    have hh := hostBound_le Q E H m hm
    simp only [List.map_cons,List.sum_cons]
    omega

theorem updated_length_le {n : ℕ} (Q E : List (Fin n × Fin n))
    (w : Sym2 (Fin n) → ℚ) (h : ℕ) (R : TypedInput n) :
    (updated Q E w h R).length≤E.length+1 := by
  unfold updated
  split <;> simp

theorem work_le_input {n : ℕ} (Q E : List (Fin n × Fin n))
    (w : Sym2 (Fin n) → ℚ) (h m : ℕ) (rs : List (TypedInput n))
    (hm : E.length+rs.length≤m) :
    work Q w h rs E≤(rs.map (candidateCap Q.length m)).sum+1 := by
  induction rs generalizing E with
  | nil => exact Nat.le_refl 1
  | cons R rs ih =>
    have he := updated_length_le Q E w h R
    have hl : (updated Q E w h R).length+rs.length≤m := by
      simp only [List.length_cons] at hm
      omega
    have hr := ih (updated Q E w h R) hl
    have hs := hostSum_le Q E R.hosts m (by omega)
    simp only [work,List.map_cons,List.sum_cons,candidateCap] at *
    omega
end LightEFTSpanners.StoredCandidates
