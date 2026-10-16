import LightEFTSpanners.StoredSortedCandidateInput

namespace LightEFTSpanners.StoredSortedCandidateInput
open Controller

def execute (weights : StoredOriginalWeightLookup.Bank) (Q : List StoredEdges.Edge)
    (bank : StoredCandidateDrawLookup.Bank) (xs : List StoredEdges.Edge) : List StoredForestBank.Input :=
  match Controller.run (transition weights Q bank) (bound weights Q bank xs) (.sorting (.sort xs [])) with
  | .records (.halt out) => out
  | _ => []

theorem execute_eq (weights : StoredOriginalWeightLookup.Bank) (Q : List StoredEdges.Edge)
    (bank : StoredCandidateDrawLookup.Bank) (xs : List StoredEdges.Edge) :
    execute weights Q bank xs=(StoredOriginalCandidateRecords.value Q bank
      (xs.mergeSort (StoredWeightComparison.result weights))).reverse := by
  obtain ⟨k,hk,ht⟩ := full_trace weights Q bank xs
  have he : bound weights Q bank xs=k+(bound weights Q bank xs-k) := by omega
  unfold execute
  rw [he,Controller.run_add,ht.run_eq,Controller.run_terminal _ _ rfl]

theorem execute_encoded {n : ℕ} (weights : StoredOriginalWeightLookup.TypedBank n) (Q : List (Fin n × Fin n))
    (bank : StoredCandidateDrawLookup.TypedBank n) (xs : List (Fin n × Fin n)) :
    execute (StoredOriginalWeightLookup.encode weights) (StoredEdges.encode Q) (StoredCandidateDrawLookup.encode bank) (StoredEdges.encode xs)=
      ((StoredOriginalCandidateRecords.typedValue Q bank (xs.mergeSort (fun x y => decide
        (StoredOriginalWeightLookup.weight s(y.1,y.2) weights≤StoredOriginalWeightLookup.weight s(x.1,x.2) weights)))).reverse).map StoredForestBank.encode := by
  rw [execute_eq]
  have h := StoredWeightSort.execute_encoded weights xs
  rw [StoredWeightSort.execute_eq] at h
  rw [h,StoredOriginalCandidateRecords.value_encoded,List.map_reverse]
end LightEFTSpanners.StoredSortedCandidateInput
