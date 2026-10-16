import LightEFTSpanners.StoredDrawLookupEncoding

namespace LightEFTSpanners.StoredForestInput

theorem attachment_encoded {n : ℕ} (fs : List (List (Fin n × Fin n)))
    (bank : StoredDrawLookup.TypedBank n) (i : ℕ) :
    StoredForestDrawAttachment.value n (StoredDrawLookup.encode bank) (StoredForestHosts.value i fs)=
      (typedInputs bank i fs).map StoredComponentRecord.encode := by
  induction fs generalizing i with
  | nil => rfl
  | cons es fs ih =>
    simp only [StoredForestHosts.value,StoredForestDrawAttachment.value,List.map_append,
      typedInputs,StoredDiscoveredHosts.value_original,List.map_map]
    congr 1
    · apply List.map_congr_left
      intro root _
      simp only [Function.comp_apply,StoredForestDrawAttachment.attached,StoredForestDrawAttachment.key,
        StoredComponentRecord.encode,StoredHosts.encode,StoredDrawLookup.value_encoded]
    · exact ih (i+1)

theorem execute_encoded {n : ℕ} (fs : List (List (Fin n × Fin n)))
    (bank : StoredDrawLookup.TypedBank n) :
    execute n (fs.map StoredEdges.encode) (StoredDrawLookup.encode bank)=
      (typedInputs bank 0 fs).map StoredComponentRecord.encode := by
  rw [execute_eq]
  exact attachment_encoded fs bank 0
end LightEFTSpanners.StoredForestInput
