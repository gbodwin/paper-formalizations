import LightEFTSpanners.StoredWeightSortBounded

namespace LightEFTSpanners.StoredWeightSort
open Controller

theorem full_trace (bank : StoredOriginalWeightLookup.Bank) (xs : List StoredEdges.Edge) :
    ∃ k,k≤bound bank xs+1 ∧ Trace (transition bank) k (.sort xs [])
      (.halt (xs.mergeSort (StoredWeightComparison.result bank))) := by
  obtain ⟨k,hk,ht⟩ := bounded_sort_trace bank xs []
  exact ⟨k+1,by omega,ht.trans (Trace.one rfl)⟩

def execute (bank : StoredOriginalWeightLookup.Bank) (xs : List StoredEdges.Edge) : List StoredEdges.Edge :=
  match Controller.run (transition bank) (bound bank xs+1) (.sort xs []) with
  | .halt out => out
  | _ => []

theorem execute_eq (bank : StoredOriginalWeightLookup.Bank) (xs : List StoredEdges.Edge) :
    execute bank xs=xs.mergeSort (StoredWeightComparison.result bank) := by
  obtain ⟨k,hk,ht⟩ := full_trace bank xs
  have he : bound bank xs+1=k+(bound bank xs+1-k) := by omega
  unfold execute
  rw [he,Controller.run_add,ht.run_eq,Controller.run_terminal _ _ rfl]
end LightEFTSpanners.StoredWeightSort
