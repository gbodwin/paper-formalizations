import LightEFTSpanners.StoredComponentCandidates
import LightEFTSpanners.StoredPreparedCandidateBound

namespace LightEFTSpanners.StoredComponentCandidates
open StoredComponentCandidate

def rawCap (n q m : ℕ) (r : Input) : ℕ :=
  (r.components.map fun x => StoredCandidates.inputHostCap n q m x.host+2).sum+3

def inputBound (n : ℕ) (Q E : List StoredEdges.Edge) (rs : List Input) : ℕ :=
  StoredComponentBank.inputBound rs+2+
    (rs.map (rawCap n Q.length (E.length+rs.length))).sum

theorem cap_le_raw {n : ℕ} (w : Sym2 (Fin n) → ℚ) (t : ℚ)
    (q m : ℕ) (r : TypedInput n) :
    StoredCandidates.candidateCap q m (StoredCandidatePreparation.typedResult w t (typedPrepared r))≤
      rawCap n q m (encode r) := by
  have hb := StoredPreparedCandidates.cap_le_raw w t q m (typedPrepared r)
  simpa only [StoredPreparedCandidates.rawCap,typedPrepared,StoredCandidatePreparation.encode,
    List.map_map,Function.comp_def,StoredHostPreparation.encode,StoredComponentRecord.typedResult,
    rawCap,encode,StoredComponentRecord.encode] using hb

theorem sum_le_raw {n : ℕ} (w : Sym2 (Fin n) → ℚ) (t : ℚ)
    (q m : ℕ) (rs : List (TypedInput n)) :
    ((rs.map fun r => StoredCandidatePreparation.typedResult w t (typedPrepared r)).map
      (StoredCandidates.candidateCap q m)).sum≤((rs.map encode).map (rawCap n q m)).sum := by
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
          (rs.map fun r => StoredCandidatePreparation.typedResult w t (typedPrepared r)) E)))) := by
  obtain ⟨k,hk,ht⟩ := prepared_trace Q E w h t rs
  have hw := StoredCandidates.work_le_input Q E w h (E.length+rs.length)
    (rs.map fun r => StoredCandidatePreparation.typedResult w t (typedPrepared r)) (by simp)
  have hr := sum_le_raw w t Q.length (E.length+rs.length) rs
  refine ⟨k,?_,ht⟩
  simp only [inputBound,StoredEdges.encode,List.length_map]
  omega
end LightEFTSpanners.StoredComponentCandidates
