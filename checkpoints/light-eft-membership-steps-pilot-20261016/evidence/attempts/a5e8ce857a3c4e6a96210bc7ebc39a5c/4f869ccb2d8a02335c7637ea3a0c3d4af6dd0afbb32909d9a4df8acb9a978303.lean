import LightEFTSpanners.StoredForestCandidates
import LightEFTSpanners.StoredForestSelectionBound

namespace LightEFTSpanners.StoredForestCandidates
open Controller

def rawHostBound (n q m : ℕ) (fs : List (List StoredEdges.Edge)) (bank : StoredDrawLookup.Bank) : ℕ :=
  (bank.map fun r => r.2.length).sum*
    (n*n*(q+m+(fs.map List.length).sum+11)+4*n+SampleVote.perSample n+5)+
    n*n*(bank.map fun r => StoredVote.drawCells r.2).sum+4

def selectionBound (n q m : ℕ) (fs : List (List StoredEdges.Edge)) (rs : List StoredForestBank.Input) : ℕ :=
  (rs.map fun r => fs.length*n*(rawHostBound n q m fs r.bank+2)+3).sum+1

def bound (n : ℕ) (fs : List (List StoredEdges.Edge)) (Q E : List StoredEdges.Edge)
    (rs : List StoredForestBank.Input) : ℕ :=
  StoredForestBank.bound n fs rs+1+selectionBound n Q.length (E.length+rs.length) fs rs

def execute (n h : ℕ) (fs : List (List StoredEdges.Edge)) (Q E : List StoredEdges.Edge)
    (W : StoredRecords.Weights) (t : ℚ) (rs : List StoredForestBank.Input) : List StoredEdges.Edge :=
  match Controller.run (transition fs Q E W n h t) (bound n fs Q E rs) (.prepare (.inputs rs [])) with
  | .select (.halt out) => out
  | _ => E

theorem raw_host_encoded {n : ℕ} (q m : ℕ) (fs : List (List (Fin n × Fin n)))
    (bank : StoredDrawLookup.TypedBank n) :
    rawHostBound n q m (fs.map StoredEdges.encode) (StoredDrawLookup.encode bank)=
      StoredForestBank.hostBound q m fs bank := by
  simp [rawHostBound,StoredForestBank.hostBound,StoredForestBank.drawCount,
    StoredForestBank.edgeCount,StoredForestBank.drawCells,StoredDrawLookup.encode,
    StoredVote.encodeDraws,StoredVote.drawCells,StoredEdges.encode,List.map_map,Function.comp_def]

theorem work_le_bound {n : ℕ} (fs : List (List (Fin n × Fin n))) (Q E : List (Fin n × Fin n))
    (w : Sym2 (Fin n) → ℚ) (h : ℕ) (t : ℚ) (rs : List (StoredForestBank.TypedInput n)) :
    StoredCandidates.work Q w h (StoredForestBank.typedValue fs w t rs) E ≤
      selectionBound n Q.length (E.length+rs.length) (fs.map StoredEdges.encode) (rs.map StoredForestBank.encode) := by
  have hw := StoredCandidates.work_le_input Q E w h (E.length+rs.length)
    (StoredForestBank.typedValue fs w t rs) (by simp [StoredForestBank.typedValue])
  apply hw.trans
  simp only [StoredForestBank.typedValue,selectionBound,List.map_map,Function.comp_def,
    StoredForestBank.encode,List.length_map,raw_host_encoded]
  apply Nat.add_le_add_right
  clear hw
  generalize E.length+rs.length = m
  induction rs with
  | nil => exact Nat.le_refl _
  | cons r rs ih =>
    have hc := StoredForestBank.candidate_cap_le Q.length m fs w t r
    simp only [List.map_cons,List.sum_cons]
    exact Nat.add_le_add hc ih

theorem full_trace {n : ℕ} (fs : List (List (Fin n × Fin n))) (Q E : List (Fin n × Fin n))
    (w : Sym2 (Fin n) → ℚ) (h : ℕ) (t : ℚ) (rs : List (StoredForestBank.TypedInput n)) :
    ∃ k, k ≤ bound n (fs.map StoredEdges.encode) (StoredEdges.encode Q) (StoredEdges.encode E)
      (rs.map StoredForestBank.encode) ∧
      Trace (transition (fs.map StoredEdges.encode) (StoredEdges.encode Q) (StoredEdges.encode E)
        (StoredRecords.encodeWeights w) n h t) k (.prepare (.inputs (rs.map StoredForestBank.encode) []))
        (.select (.halt (StoredEdges.encode (StoredCandidates.selected Q w h (StoredForestBank.typedValue fs w t rs) E)))) := by
  obtain ⟨k,hk,ht⟩ := prepared_trace fs Q E w h t rs
  have hb := work_le_bound fs Q E w h t rs
  exact ⟨k,by simp only [bound,StoredEdges.encode,List.length_map];omega,ht⟩

theorem execute_encoded {n : ℕ} (fs : List (List (Fin n × Fin n))) (Q E : List (Fin n × Fin n))
    (w : Sym2 (Fin n) → ℚ) (h : ℕ) (t : ℚ) (rs : List (StoredForestBank.TypedInput n)) :
    execute n h (fs.map StoredEdges.encode) (StoredEdges.encode Q) (StoredEdges.encode E)
      (StoredRecords.encodeWeights w) t (rs.map StoredForestBank.encode)=
      StoredEdges.encode (StoredCandidates.selected Q w h (StoredForestBank.typedValue fs w t rs) E) := by
  obtain ⟨k,hk,ht⟩ := full_trace fs Q E w h t rs
  have he : bound n (fs.map StoredEdges.encode) (StoredEdges.encode Q) (StoredEdges.encode E)
      (rs.map StoredForestBank.encode)=k+(bound n (fs.map StoredEdges.encode)
        (StoredEdges.encode Q) (StoredEdges.encode E) (rs.map StoredForestBank.encode)-k) := by omega
  unfold execute
  rw [he,Controller.run_add,ht.run_eq,Controller.run_terminal _ _ rfl]
end LightEFTSpanners.StoredForestCandidates
