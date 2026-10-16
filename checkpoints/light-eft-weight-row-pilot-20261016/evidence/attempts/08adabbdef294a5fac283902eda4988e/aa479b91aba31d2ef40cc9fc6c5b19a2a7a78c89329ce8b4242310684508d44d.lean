import LightEFTSpanners.StoredOriginalGraphExecution

namespace LightEFTSpanners.StoredOriginalGraphCaller
open Controller

def execute (n h : ℕ) (fs : List (List StoredEdges.Edge)) (Q E xs : List StoredEdges.Edge)
    (weights : StoredOriginalWeightLookup.Bank) (bank : StoredCandidateDrawLookup.Bank) (t : ℚ) : List StoredEdges.Edge :=
  match Controller.run (transition n h fs Q E weights bank t) (bound n fs Q E xs weights bank)
    (.prepare (.sorting (.sort xs []))) with
  | .run _ (.candidates _ (.select (.halt out))) => out
  | _ => E

theorem execute_encoded {n : ℕ} (h : ℕ) (fs : List (List (Fin n × Fin n))) (Q E xs : List (Fin n × Fin n))
    (weights : StoredOriginalWeightLookup.TypedBank n) (bank : StoredCandidateDrawLookup.TypedBank n) (t : ℚ) :
    execute n h (fs.map StoredEdges.encode) (StoredEdges.encode Q) (StoredEdges.encode E) (StoredEdges.encode xs)
      (StoredOriginalWeightLookup.encode weights) (StoredCandidateDrawLookup.encode bank) t=
      StoredEdges.encode (StoredCandidates.selected Q (fun e => StoredOriginalWeightLookup.weight e weights) h
        (StoredForestBank.typedValue fs (fun e => StoredOriginalWeightLookup.weight e weights) t
          (prepared weights Q bank xs)) E) := by
  obtain ⟨k,hk,ht⟩ := full_trace h fs Q E xs weights bank t
  let B := bound n (fs.map StoredEdges.encode) (StoredEdges.encode Q) (StoredEdges.encode E) (StoredEdges.encode xs)
    (StoredOriginalWeightLookup.encode weights) (StoredCandidateDrawLookup.encode bank)
  have he : B=k+(B-k) := by omega
  unfold execute
  change (match Controller.run _ B (State.prepare (.sorting (.sort (StoredEdges.encode xs) []))) with
    | State.run _ (.candidates _ (.select (.halt out))) => out | _ => _) = _
  rw [he,Controller.run_add,ht.run_eq,Controller.run_terminal _ _ rfl]

theorem execute_composed {n : ℕ} (h : ℕ) (fs : List (List (Fin n × Fin n))) (Q E xs : List (Fin n × Fin n))
    (weights : StoredOriginalWeightLookup.TypedBank n) (bank : StoredCandidateDrawLookup.TypedBank n) (t : ℚ) :
    execute n h (fs.map StoredEdges.encode) (StoredEdges.encode Q) (StoredEdges.encode E) (StoredEdges.encode xs)
      (StoredOriginalWeightLookup.encode weights) (StoredCandidateDrawLookup.encode bank) t=
      StoredWeightedForestCandidates.execute n h (fs.map StoredEdges.encode) (StoredEdges.encode Q) (StoredEdges.encode E)
        (StoredOriginalWeightLookup.encode weights) t
        (StoredSortedCandidateInput.execute (StoredOriginalWeightLookup.encode weights) (StoredEdges.encode Q)
          (StoredCandidateDrawLookup.encode bank) (StoredEdges.encode xs)) := by
  rw [StoredSortedCandidateInput.execute_encoded]
  change _=StoredWeightedForestCandidates.execute _ _ _ _ _ _ _ ((prepared weights Q bank xs).map StoredForestBank.encode)
  rw [StoredWeightedForestCandidates.execute_encoded,execute_encoded]
end LightEFTSpanners.StoredOriginalGraphCaller
