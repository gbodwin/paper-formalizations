import LightEFTSpanners.StoredForestCandidatesExecutable
import LightEFTSpanners.StoredComponentOriginal

namespace LightEFTSpanners.StoredCanonicalComponents
attribute [local instance] Classical.propDecidable

theorem component_root_exists {n : ℕ} (edges : List (Fin n × Fin n))
    (c : (ExecutableVoting.graph (StoredSample.edgeSet edges)).ConnectedComponent) :
    ∃ root,root∈roots edges ∧ (ExecutableVoting.graph (StoredSample.edgeSet edges)).connectedComponentMk root=c := by
  exact List.mem_map.mp (indices_all edges c)

noncomputable def componentRoot {n : ℕ} (edges : List (Fin n × Fin n))
    (c : (ExecutableVoting.graph (StoredSample.edgeSet edges)).ConnectedComponent) : Fin n :=
  Classical.choose (component_root_exists edges c)

theorem componentRoot_mem {n : ℕ} (edges : List (Fin n × Fin n))
    (c : (ExecutableVoting.graph (StoredSample.edgeSet edges)).ConnectedComponent) :
    componentRoot edges c∈roots edges := (Classical.choose_spec (component_root_exists edges c)).1

theorem componentRoot_eq {n : ℕ} (edges : List (Fin n × Fin n))
    (c : (ExecutableVoting.graph (StoredSample.edgeSet edges)).ConnectedComponent) :
    (ExecutableVoting.graph (StoredSample.edgeSet edges)).connectedComponentMk (componentRoot edges c)=c :=
  (Classical.choose_spec (component_root_exists edges c)).2

theorem componentRoot_mk {n : ℕ} (edges : List (Fin n × Fin n)) (root : Fin n)
    (hr : root∈roots edges) :
    componentRoot edges ((ExecutableVoting.graph (StoredSample.edgeSet edges)).connectedComponentMk root)=root := by
  have hreach := SimpleGraph.ConnectedComponent.exact (componentRoot_eq edges
    ((ExecutableVoting.graph (StoredSample.edgeSet edges)).connectedComponentMk root))
  have he := representative_eq edges _ root hreach
  rw [(mem_roots edges _).mp (componentRoot_mem edges _),(mem_roots edges root).mp hr] at he
  exact he

theorem componentRoot_vertices {n : ℕ} (edges : List (Fin n × Fin n))
    (c : (ExecutableVoting.graph (StoredSample.edgeSet edges)).ConnectedComponent) (v : Fin n) :
    v∈StoredEdgeComponent.vertices edges (componentRoot edges c) ↔ v∈c.supp := by
  rw [StoredEdgeComponent.vertices_component,componentRoot_eq]
end LightEFTSpanners.StoredCanonicalComponents
