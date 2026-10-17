import LightEFTSpanners.StoredEdgeComponent

namespace LightEFTSpanners.StoredEdgeComponent

def vertices {n : ℕ} (edges : List (Fin n × Fin n)) (root : Fin n) : List (Fin n) :=
  (List.finRange n).filter (StoredReachability.test (ExecutableVoting.graph (StoredSample.edgeSet edges)) root)

theorem execute_vertices {n : ℕ} (edges : List (Fin n × Fin n)) (root : Fin n) :
    execute n root.val (StoredEdges.encode edges)=(vertices edges root).map Fin.val := execute_eq edges root

theorem vertices_nodup {n : ℕ} (edges : List (Fin n × Fin n)) (root : Fin n) :
    (vertices edges root).Nodup := (List.nodup_finRange n).filter _

theorem mem_vertices {n : ℕ} (edges : List (Fin n × Fin n)) (root v : Fin n) :
    v∈vertices edges root ↔ (ExecutableVoting.graph (StoredSample.edgeSet edges)).Reachable root v := by
  simp [vertices,StoredReachability.test_iff]

theorem vertices_component {n : ℕ} (edges : List (Fin n × Fin n)) (root v : Fin n) :
    v∈vertices edges root ↔
      v∈((ExecutableVoting.graph (StoredSample.edgeSet edges)).connectedComponentMk root).supp := by
  rw [mem_vertices,SimpleGraph.ConnectedComponent.mem_supp_iff,SimpleGraph.ConnectedComponent.eq]
  exact ⟨SimpleGraph.Reachable.symm,SimpleGraph.Reachable.symm⟩

theorem represented_component {n : ℕ} (F : SimpleGraph (Fin n))
    (edges : List (Fin n × Fin n)) (hF : ExecutableVoting.graph (StoredSample.edgeSet edges)=F)
    (root v : Fin n) :
    v.val∈execute n root.val (StoredEdges.encode edges) ↔ v∈(F.connectedComponentMk root).supp := by
  rw [execute_mem,←hF,SimpleGraph.ConnectedComponent.mem_supp_iff,SimpleGraph.ConnectedComponent.eq]
  exact ⟨SimpleGraph.Reachable.symm,SimpleGraph.Reachable.symm⟩
end LightEFTSpanners.StoredEdgeComponent
