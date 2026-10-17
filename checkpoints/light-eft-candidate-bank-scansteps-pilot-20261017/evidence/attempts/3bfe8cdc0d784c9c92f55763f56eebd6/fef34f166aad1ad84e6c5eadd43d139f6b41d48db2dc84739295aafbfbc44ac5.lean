import LightEFTSpanners.StoredCanonicalPartition

namespace LightEFTSpanners.StoredCanonicalComponents
attribute [local instance] Classical.propDecidable

def indices {n : ℕ} (edges : List (Fin n × Fin n)) :
    List (ExecutableVoting.graph (StoredSample.edgeSet edges)).ConnectedComponent :=
  (roots edges).map (ExecutableVoting.graph (StoredSample.edgeSet edges)).connectedComponentMk

theorem indices_nodup {n : ℕ} (edges : List (Fin n × Fin n)) : (indices edges).Nodup := by
  apply (roots_nodup edges).map_on
  intro u hu v hv he
  have hreach := SimpleGraph.ConnectedComponent.exact he
  have h := representative_eq edges u v hreach
  rwa [(mem_roots edges u).mp hu,(mem_roots edges v).mp hv] at h

theorem indices_all {n : ℕ} (edges : List (Fin n × Fin n)) :
    ∀ c : (ExecutableVoting.graph (StoredSample.edgeSet edges)).ConnectedComponent,c∈indices edges := by
  refine (SimpleGraph.ConnectedComponent.forall
    (G:=ExecutableVoting.graph (StoredSample.edgeSet edges)) (p:=fun c => c∈indices edges)).mpr ?_
  intro v
  exact List.mem_map.mpr ⟨representative edges v,
    (mem_roots edges _).mpr (representative_fixed edges v),
    (SimpleGraph.ConnectedComponent.sound (representative_reachable edges v)).symm⟩

theorem indices_univ {n : ℕ} (edges : List (Fin n × Fin n)) : (indices edges).toFinset=Finset.univ := by
  classical
  exact Finset.eq_univ_of_forall fun c => List.mem_toFinset.mpr (indices_all edges c)
end LightEFTSpanners.StoredCanonicalComponents
