import LightEFTSpanners.StoredWeightSortExecutable

namespace LightEFTSpanners.StoredWeightSort

theorem execute_encoded {n : ℕ} (bank : StoredOriginalWeightLookup.TypedBank n)
    (xs : List (Fin n × Fin n)) :
    execute (StoredOriginalWeightLookup.encode bank) (StoredEdges.encode xs)=
      StoredEdges.encode (xs.mergeSort (fun x y => decide
        (StoredOriginalWeightLookup.weight s(y.1,y.2) bank≤StoredOriginalWeightLookup.weight s(x.1,x.2) bank))) := by
  rw [execute_eq]
  symm
  apply List.map_mergeSort
  intro x _ y _
  exact (StoredWeightComparison.result_encoded bank x y).symm
end LightEFTSpanners.StoredWeightSort
