import LightEFTSpanners.StoredForestInputEncoding

namespace LightEFTSpanners.StoredForestInput

theorem value_length {n : ℕ} (fs : List (List (Fin n × Fin n))) (bank : StoredDrawLookup.Bank) :
    (value fs bank).length≤fs.length*n := by
  simpa [value,StoredForestDrawAttachment.value] using StoredForestHosts.value_length fs 0

theorem vertices_length {n : ℕ} (fs : List (List (Fin n × Fin n))) (bank : StoredDrawLookup.Bank)
    (r : StoredComponentRecord.Input) (h : r∈value fs bank) : r.vertices.length≤n := by
  obtain ⟨rec,hr,rfl⟩ := List.mem_map.mp h
  obtain ⟨j,es,root,_,_,rfl⟩ := (StoredForestHosts.mem_value fs 0 rec).mp hr
  simp only [StoredForestDrawAttachment.attached,StoredForestHosts.componentRecord,List.length_map]
  simpa [StoredEdgeComponent.vertices] using List.length_filter_le
    (StoredReachability.test (ExecutableVoting.graph (StoredSample.edgeSet es)) root) (List.finRange n)
end LightEFTSpanners.StoredForestInput
