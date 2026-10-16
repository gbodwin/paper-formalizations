import LightEFTSpanners.StoredComponentHostEncoding

namespace LightEFTSpanners.StoredComponentHostFilter
open SimpleGraph
attribute [local instance] Classical.propDecidable

theorem typedValue_component {n : ℕ} (edges : List (Fin n × Fin n)) (root : Fin n) :
    StoredSample.edgeSet (typedValue (StoredEdgeComponent.vertices edges root) edges)=
      (((ExecutableVoting.graph (StoredSample.edgeSet edges)).connectedComponentMk root).toSimpleGraph.map
        (componentEmbedding (ExecutableVoting.graph (StoredSample.edgeSet edges))
          ((ExecutableVoting.graph (StoredSample.edgeSet edges)).connectedComponentMk root))).edgeFinset := by
  classical
  ext e
  obtain ⟨u,v⟩ := e
  rw [mem_host_iff,mem_edgeFinset,mem_edgeSet,component_mapped_adj,
    StoredEdgeComponent.vertices_component,StoredEdgeComponent.vertices_component]
  constructor
  · rintro ⟨hne,hu,_,he⟩
    exact ⟨hu,he,hne⟩
  · rintro ⟨hu,hadj⟩
    have hv := (ConnectedComponent.mem_supp_congr_adj
      ((ExecutableVoting.graph (StoredSample.edgeSet edges)).connectedComponentMk root) hadj).mp hu
    exact ⟨hadj.2,hu,hv,hadj.1⟩
end LightEFTSpanners.StoredComponentHostFilter
