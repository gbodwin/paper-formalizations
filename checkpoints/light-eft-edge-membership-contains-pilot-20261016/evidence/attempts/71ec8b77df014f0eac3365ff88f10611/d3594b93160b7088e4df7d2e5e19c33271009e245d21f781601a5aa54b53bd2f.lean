import LightEFTSpanners.StoredForestIndexedRecords

namespace LightEFTSpanners.StoredForestCandidates
attribute [local instance] Classical.propDecidable

noncomputable def componentId {n q : ℕ} (edges : Fin q → List (Fin n × Fin n))
    (j : ForestComponentIndex (StoredForestHosts.family edges)) : ℕ :=
  (StoredForestInput.indexedRecord edges [] j).id
noncomputable def componentVertices {n q : ℕ} (edges : Fin q → List (Fin n × Fin n))
    (j : ForestComponentIndex (StoredForestHosts.family edges)) : List (Fin n) :=
  (StoredForestInput.indexedRecord edges [] j).vertices
noncomputable def hostInput {n q : ℕ} (edges : Fin q → List (Fin n × Fin n))
    (banks : Sym2 (Fin n) → StoredDrawLookup.TypedBank n) (e : Sym2 (Fin n))
    (j : ForestComponentIndex (StoredForestHosts.family edges)) : StoredHosts.TypedInput n :=
  (StoredForestInput.indexedRecord edges (banks e) j).host

def rawInputs {n : ℕ} (banks : Sym2 (Fin n) → StoredDrawLookup.TypedBank n)
    (es : List (Fin n × Fin n)) : List (StoredForestBank.TypedInput n) :=
  es.map fun e => ⟨e,banks s(e.1,e.2)⟩

theorem indexed_prepared {n q : ℕ} (edges : Fin q → List (Fin n × Fin n))
    (banks : Sym2 (Fin n) → StoredDrawLookup.TypedBank n)
    (w : Sym2 (Fin n) → ℚ) (t : ℚ) (es : List (Fin n × Fin n)) :
    StoredForestBank.typedValue (List.ofFn edges) w t (rawInputs banks es)=
      (StoredComponentCandidates.indexedRecords (componentId edges) (componentVertices edges)
        (hostInput edges banks) (StoredForestHosts.indices edges) es).map
        (fun r => StoredCandidatePreparation.typedResult w t (StoredComponentCandidate.typedPrepared r)) := by
  simp only [StoredForestBank.typedValue,rawInputs,StoredComponentCandidates.indexedRecords,List.map_map]
  apply List.map_congr_left
  intro e _
  simp only [Function.comp_apply,StoredForestCandidate.typedResult,StoredForestInput.typedInputs_indexed]
  congr 2

theorem execute_forest_assignment {n m q : ℕ} (edges : Fin (q+1) → List (Fin n × Fin n))
    (Q : List (Fin n × Fin n)) (w : Sym2 (Fin n) → ℚ) (hw : ∀ e,0≤w e) (t : ℚ)
    (a : SampledGreedy.Assignment (Fin n) (ForestComponentIndex (StoredForestHosts.family edges)) m)
    (h : ℕ) (banks : Sym2 (Fin n) → StoredDrawLookup.TypedBank n) (es : List (Fin n × Fin n))
    (hd : ∀ e∈es,∀ j∈StoredForestHosts.indices edges,
      ((hostInput edges banks s(e.1,e.2) j).draws.map StoredSample.edgeSet)=List.ofFn (a s(e.1,e.2) j)) :
    ∃ out : List (Fin n × Fin n),
      execute n h ((List.ofFn edges).map StoredEdges.encode) (StoredEdges.encode Q) (StoredEdges.encode Q)
        (StoredRecords.encodeWeights w) t ((rawInputs banks es).map StoredForestBank.encode)=StoredEdges.encode out ∧
      StoredSample.edgeSet out=SampledGreedy.edges (StoredSample.edgeSet Q) (fun d => (w d:ℝ)) (t:ℝ)
        (SampledGreedy.componentEligible Finset.univ (StoredForestHosts.family edges))
        (SampledGreedy.componentHost (StoredForestHosts.family edges)) (SampledGreedy.assignmentTape a) h
        (es.map fun e => s(e.1,e.2)).reverse := by
  obtain ⟨out,he,ho⟩ := StoredComponentCandidates.execute_forest_assignment Q w hw t
    (StoredForestHosts.family edges) a h (componentId edges) (componentVertices edges)
    (hostInput edges banks) (StoredForestHosts.indices edges) es
    (StoredForestHosts.indices_nodup edges) (StoredForestHosts.indices_univ edges)
    (fun j v => StoredForestInput.indexed_vertices edges [] j v)
    (fun e _ j _ => (StoredForestInput.indexed_host edges (banks s(e.1,e.2)) j).symm) hd
  refine ⟨out,?_,ho⟩
  rw [execute_encoded,indexed_prepared]
  rw [StoredComponentCandidates.execute_encoded] at he
  exact he
end LightEFTSpanners.StoredForestCandidates
