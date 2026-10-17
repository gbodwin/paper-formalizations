import LightEFTSpanners.StoredForestInputIndices

namespace LightEFTSpanners.StoredForestInput
attribute [local instance] Classical.propDecidable

noncomputable def indexedRecord {n q : ℕ} (edges : Fin q → List (Fin n × Fin n))
    (bank : StoredDrawLookup.TypedBank n) (j : ForestComponentIndex (StoredForestHosts.family edges)) :
    StoredComponentRecord.TypedInput n := componentRecord bank j.1.val (edges j.1) j.2

theorem typedInputs_indexed {n q : ℕ} (edges : Fin q → List (Fin n × Fin n))
    (bank : StoredDrawLookup.TypedBank n) :
    typedInputs bank 0 (List.ofFn edges)=
      (StoredForestHosts.indices edges).map (indexedRecord edges bank) := by
  rw [typedInputs_ofFn]
  simp only [StoredForestHosts.indices,List.map_flatMap]
  congr 1
  funext i
  simp only [Nat.zero_add]
  rw [←component_records bank i.val (edges i)]
  symm
  exact List.map_map (g:=indexedRecord edges bank) (f:=Sigma.mk i) (l:=StoredCanonicalComponents.indices (edges i))

theorem indexed_vertices {n q : ℕ} (edges : Fin q → List (Fin n × Fin n))
    (bank : StoredDrawLookup.TypedBank n) (j : ForestComponentIndex (StoredForestHosts.family edges))
    (v : Fin n) : v∈(indexedRecord edges bank j).vertices ↔ v∈j.2.supp :=
  StoredCanonicalComponents.componentRoot_vertices (edges j.1) j.2 v

theorem indexed_host {n q : ℕ} (edges : Fin q → List (Fin n × Fin n))
    (bank : StoredDrawLookup.TypedBank n) (j : ForestComponentIndex (StoredForestHosts.family edges)) :
    StoredSample.edgeSet (indexedRecord edges bank j).host.edges=
      SampledGreedy.componentHost (StoredForestHosts.family edges) j := by
  rcases j with ⟨i,c⟩
  change (ExecutableVoting.graph (StoredSample.edgeSet (edges i))).ConnectedComponent at c
  change StoredSample.edgeSet (StoredDiscoveredHosts.typedHost (edges i)
    (StoredCanonicalComponents.componentRoot (edges i) c))=_
  rw [StoredDiscoveredHosts.host_component,StoredCanonicalComponents.componentRoot_eq]
  rfl
end LightEFTSpanners.StoredForestInput
