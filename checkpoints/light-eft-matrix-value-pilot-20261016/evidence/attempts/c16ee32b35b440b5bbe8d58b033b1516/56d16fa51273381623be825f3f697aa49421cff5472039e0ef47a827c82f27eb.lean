import LightEFTSpanners.StoredDiscoveredHostsTrace

namespace LightEFTSpanners.StoredDiscoveredHosts
attribute [local instance] Classical.propDecidable

def typedHost {n : ℕ} (edges : List (Fin n × Fin n)) (root : Fin n) : List (Fin n × Fin n) :=
  StoredComponentHostFilter.typedValue (StoredEdgeComponent.vertices edges root) edges

theorem value_original {n : ℕ} (edges : List (Fin n × Fin n)) :
    value edges=(StoredCanonicalComponents.roots edges).map fun root =>
      ((root.val,(StoredEdgeComponent.vertices edges root).map Fin.val),StoredEdges.encode (typedHost edges root)) := by
  simp only [value,StoredCanonicalHosts.value,StoredCanonicalEnumeration.records,List.map_map]
  apply List.map_congr_left
  intro root _
  simp only [Function.comp_apply,StoredComponentHostFilter.value_encoded,typedHost]

theorem execute_original {n : ℕ} (edges : List (Fin n × Fin n)) :
    execute n (StoredEdges.encode edges)=(StoredCanonicalComponents.roots edges).map fun root =>
      ((root.val,(StoredEdgeComponent.vertices edges root).map Fin.val),StoredEdges.encode (typedHost edges root)) := by
  rw [execute_eq,value_original]

theorem host_component {n : ℕ} (edges : List (Fin n × Fin n)) (root : Fin n) :
    StoredSample.edgeSet (typedHost edges root)=
      (((ExecutableVoting.graph (StoredSample.edgeSet edges)).connectedComponentMk root).toSimpleGraph.map
        (componentEmbedding (ExecutableVoting.graph (StoredSample.edgeSet edges))
          ((ExecutableVoting.graph (StoredSample.edgeSet edges)).connectedComponentMk root))).edgeFinset :=
  StoredComponentHostFilter.typedValue_component edges root

theorem execute_components {n : ℕ} (edges : List (Fin n × Fin n)) :
    (execute n (StoredEdges.encode edges)).map Prod.fst=StoredCanonicalEnumeration.records edges := by
  rw [execute_eq]
  simp [value,StoredCanonicalHosts.value,List.map_map,Function.comp_def]
end LightEFTSpanners.StoredDiscoveredHosts
