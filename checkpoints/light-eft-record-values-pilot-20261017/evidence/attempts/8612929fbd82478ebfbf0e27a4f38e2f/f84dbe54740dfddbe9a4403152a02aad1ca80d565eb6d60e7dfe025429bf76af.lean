import LightEFTSpanners.StoredPreparedCandidates

namespace LightEFTSpanners.StoredPreparedCandidates
open StoredCandidatePreparation

def rawCap (n q m : ℕ) (r : Input) : ℕ :=
  (r.catalogue.map fun x => StoredCandidates.inputHostCap n q m x.host+2).sum+3

def inputBound (n : ℕ) (Q E : List StoredEdges.Edge) (rs : List Input) : ℕ :=
  StoredCandidateBankPreparation.inputBound rs+2+
    (rs.map (rawCap n Q.length (E.length+rs.length))).sum

theorem cap_le_raw {n : ℕ} (w : Sym2 (Fin n) → ℚ) (t : ℚ)
    (q m : ℕ) (r : TypedInput n) :
    StoredCandidates.candidateCap q m (typedResult w t r)≤rawCap n q m (encode r) := by
  have hf := StoredPreparedHostVote.filter_sum_le
    (StoredHostPreparation.eligible r.edge.1 r.edge.2)
    (fun x : StoredHostPreparation.TypedRecord n => StoredCandidates.hostCap q m x.host+2) r.catalogue
  simpa only [StoredCandidates.candidateCap,typedResult,rawCap,encode,
    List.map_map,Function.comp_def,StoredHostPreparation.encode,StoredCandidates.inputHostCap,
    StoredCandidates.hostCap,StoredHosts.encode,StoredEdges.encode,StoredVote.encodeDraws,
    StoredVote.drawCells,List.length_map,Nat.add_le_add_iff_right] using hf

theorem sum_le_raw {n : ℕ} (w : Sym2 (Fin n) → ℚ) (t : ℚ)
    (q m : ℕ) (rs : List (TypedInput n)) :
    ((rs.map (typedResult w t)).map (StoredCandidates.candidateCap q m)).sum≤
      ((rs.map encode).map (rawCap n q m)).sum := by
  induction rs with
  | nil => exact Nat.le_refl 0
  | cons r rs ih =>
    have hr := cap_le_raw w t q m r
    simp only [List.map_cons,List.sum_cons]
    omega

theorem bounded_trace {n : ℕ} (Q E : List (Fin n × Fin n))
    (w : Sym2 (Fin n) → ℚ) (h : ℕ) (t : ℚ) (rs : List (TypedInput n)) :
    ∃ k,k ≤ inputBound n (StoredEdges.encode Q) (StoredEdges.encode E) (rs.map encode) ∧
      Controller.Trace (transition (StoredEdges.encode Q) (StoredEdges.encode E)
        (StoredRecords.encodeWeights w) n h t) k
        (.prepare (.inputs (rs.map encode) []))
        (.select (.halt (StoredEdges.encode (StoredCandidates.selected Q w h
          (rs.map (typedResult w t)) E)))) := by
  obtain ⟨k,hk,ht⟩ := prepared_trace Q E w h t rs
  have hw := StoredCandidates.work_le_input Q E w h (E.length+rs.length)
    (rs.map (typedResult w t)) (by simp)
  have hr := sum_le_raw w t Q.length (E.length+rs.length) rs
  refine ⟨k,?_,ht⟩
  simp only [inputBound,StoredEdges.encode,List.length_map]
  omega
end LightEFTSpanners.StoredPreparedCandidates
