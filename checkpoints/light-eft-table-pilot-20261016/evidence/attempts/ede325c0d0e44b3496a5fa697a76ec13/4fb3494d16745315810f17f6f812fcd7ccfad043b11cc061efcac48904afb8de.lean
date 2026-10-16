import LightEFTSpanners.StoredDiscoveredHosts

namespace LightEFTSpanners.StoredDiscoveredHosts
open Controller

theorem records_length {n : ℕ} (edges : List (Fin n × Fin n)) :
    (StoredCanonicalEnumeration.records edges).length≤n := by
  simp only [StoredCanonicalEnumeration.records,List.length_map]
  simpa [StoredCanonicalComponents.roots] using List.length_filter_le
    (fun r : Fin n => decide (StoredCanonicalComponents.representative edges r=r)) (List.finRange n)

theorem vertices_length {n : ℕ} (edges : List (Fin n × Fin n))
    (r : StoredCanonicalEnumeration.Record) (h : r∈StoredCanonicalEnumeration.records edges) : r.2.length≤n := by
  rcases r with ⟨r,vs⟩
  obtain ⟨root,_,_,rfl⟩ := (StoredCanonicalEnumeration.mem_records edges r vs).mp h
  simp only [List.length_map]
  simpa [StoredEdgeComponent.vertices] using List.length_filter_le
    (StoredReachability.test (ExecutableVoting.graph (StoredSample.edgeSet edges)) root) (List.finRange n)

theorem full_trace {n : ℕ} (edges : List (Fin n × Fin n)) :
    ∃ k,k≤bound n edges.length ∧ Trace (transition n (StoredEdges.encode edges)) k
      (.components (.range n [])) (.halt (value edges)) := by
  obtain ⟨k,hk,ht⟩ := StoredCanonicalEnumeration.full_trace edges
  have he : StoredCanonicalEnumeration.values edges (List.finRange n)=StoredCanonicalEnumeration.records edges := by
    rw [StoredCanonicalEnumeration.values_eq]
    rfl
  rw [he] at ht
  have a := components_lift n (StoredEdges.encode edges) ht
  have b := Trace.one (show transition n (StoredEdges.encode edges)
    (.components (.halt (StoredCanonicalEnumeration.records edges)))=
      some (.hosts (.records (StoredCanonicalEnumeration.records edges) [])) from rfl)
  have c := hosts_lift n (StoredEdges.encode edges)
    (StoredCanonicalHosts.hosts_trace (StoredEdges.encode edges) (StoredCanonicalEnumeration.records edges))
  have d := Trace.one (show transition n (StoredEdges.encode edges) (.hosts (.halt (value edges)))=
    some (.halt (value edges)) from rfl)
  have hs := StoredCanonicalHosts.steps_le (StoredEdges.encode edges)
    (StoredCanonicalEnumeration.records edges) n (vertices_length edges)
  have hl := records_length edges
  have hm : StoredCanonicalHosts.bound n (StoredEdges.encode edges).length
      (StoredCanonicalEnumeration.records edges).length≤StoredCanonicalHosts.bound n edges.length n := by
    simp only [StoredEdges.encode,List.length_map]
    unfold StoredCanonicalHosts.bound
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hl) _
  refine ⟨k+1+StoredCanonicalHosts.steps (StoredEdges.encode edges) (StoredCanonicalEnumeration.records edges)+1,?_,?_⟩
  · unfold bound
    omega
  · simpa [value,Nat.add_assoc] using a.trans (b.trans (c.trans d))

theorem execute_eq {n : ℕ} (edges : List (Fin n × Fin n)) :
    execute n (StoredEdges.encode edges)=value edges := by
  obtain ⟨k,hk,ht⟩ := full_trace edges
  have he : bound n (StoredEdges.encode edges).length=k+(bound n (StoredEdges.encode edges).length-k) := by
    simp only [StoredEdges.encode,List.length_map]
    omega
  unfold execute
  rw [he,Controller.run_add,ht.run_eq,Controller.run_terminal _ _ rfl]
end LightEFTSpanners.StoredDiscoveredHosts
