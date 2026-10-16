import LightEFTSpanners.StoredForestDrawSize

namespace LightEFTSpanners.StoredForestBank

def edgeCount {n : ℕ} (fs : List (List (Fin n × Fin n))) : ℕ := (fs.map List.length).sum

theorem typed_inputs_length {n : ℕ} (fs : List (List (Fin n × Fin n)))
    (bank : StoredDrawLookup.TypedBank n) (i : ℕ) :
    (StoredForestInput.typedInputs bank i fs).length ≤ fs.length*n := by
  induction fs generalizing i with
  | nil => simp [StoredForestInput.typedInputs]
  | cons es fs ih =>
    have hr : (StoredCanonicalComponents.roots es).length ≤ n := by
      simpa [StoredCanonicalComponents.roots] using List.length_filter_le
        (fun r => decide (StoredCanonicalComponents.representative es r=r)) (List.finRange n)
    have ht := ih (i+1)
    simp only [StoredForestInput.typedInputs,List.length_append,List.length_map,List.length_cons]
    nlinarith

theorem input_host_size {n : ℕ} (fs : List (List (Fin n × Fin n)))
    (bank : StoredDrawLookup.TypedBank n) (i : ℕ) (r : StoredComponentRecord.TypedInput n)
    (hr : r∈StoredForestInput.typedInputs bank i fs) :
    r.host.edges.length ≤ edgeCount fs ∧ r.host.draws.length ≤ drawCount bank ∧
      (r.host.draws.map List.length).sum ≤ drawCells bank := by
  induction fs generalizing i with
  | nil => simp [StoredForestInput.typedInputs] at hr
  | cons es fs ih =>
    simp only [StoredForestInput.typedInputs,List.mem_append] at hr
    rcases hr with hr | hr
    · obtain ⟨root,_,rfl⟩ := List.mem_map.mp hr
      have he : (StoredDiscoveredHosts.typedHost es root).length ≤ es.length :=
        List.length_filter_le _ _
      exact ⟨by simpa only [edgeCount,List.map_cons,List.sum_cons] using
        le_trans he (Nat.le_add_right _ _),lookup_count _ bank,lookup_cells _ bank⟩
    · obtain ⟨he,hd,hc⟩ := ih (i+1) hr
      exact ⟨by simp only [edgeCount,List.map_cons,List.sum_cons] at *;omega,hd,hc⟩
end LightEFTSpanners.StoredForestBank
