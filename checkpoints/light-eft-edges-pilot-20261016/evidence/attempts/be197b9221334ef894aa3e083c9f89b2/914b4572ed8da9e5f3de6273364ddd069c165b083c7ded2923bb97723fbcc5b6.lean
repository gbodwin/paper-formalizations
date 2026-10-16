import LightEFTSpanners.StoredComponentCandidateExecutable
import LightEFTSpanners.StoredPreparedCandidateAssignment
import LightEFTSpanners.ConstructedVotingHosts

namespace LightEFTSpanners.StoredComponentCandidates
open StoredComponentCandidate
attribute [local instance] Classical.propDecidable

def indexedRecords {n : ℕ} {J : Type*} (id : J → ℕ) (vertices : J → List (Fin n))
    (input : Sym2 (Fin n) → J → StoredHosts.TypedInput n) (js : List J)
    (es : List (Fin n × Fin n)) : List (TypedInput n) :=
  es.map fun e => ⟨e,js.map fun j => ⟨id j,vertices j,input s(e.1,e.2) j⟩⟩

theorem indexed_prepared {n : ℕ} {J : Type*} (id : J → ℕ) (vertices : J → List (Fin n))
    (input : Sym2 (Fin n) → J → StoredHosts.TypedInput n) (js : List J)
    (es : List (Fin n × Fin n)) :
    (indexedRecords id vertices input js es).map typedPrepared=
      StoredPreparedCandidates.indexedRecords id
        (fun j => StoredVertexPairs.typedPairs (vertices j) (vertices j)) input js es := by
  simp only [indexedRecords,typedPrepared,StoredPreparedCandidates.indexedRecords,
    StoredPreparedHostVote.catalogue,StoredComponentRecord.typedResult,List.map_map,Function.comp_def]

/-- Full component vertex enumerations generate component eligibility inside
actual execution. Original host/draw representations remain explicit. -/
theorem execute_forest_assignment {n m q : ℕ}
    (Q : List (Fin n × Fin n)) (w : Sym2 (Fin n) → ℚ) (hw : ∀ e,0≤w e) (t : ℚ)
    (F : Fin (q+1) → SimpleGraph (Fin n))
    (a : SampledGreedy.Assignment (Fin n) (ForestComponentIndex F) m) (h : ℕ)
    (id : ForestComponentIndex F → ℕ) (vertices : ForestComponentIndex F → List (Fin n))
    (input : Sym2 (Fin n) → ForestComponentIndex F → StoredHosts.TypedInput n)
    (js : List (ForestComponentIndex F)) (es : List (Fin n × Fin n)) (hj : js.Nodup)
    (hall : js.toFinset=Finset.univ)
    (hv : ∀ j,∀ v,v∈vertices j ↔ v∈j.2.supp)
    (hh : ∀ e∈es,∀ j∈js,SampledGreedy.componentHost F j=StoredSample.edgeSet (input s(e.1,e.2) j).edges)
    (hd : ∀ e∈es,∀ j∈js,
      ((input s(e.1,e.2) j).draws.map StoredSample.edgeSet)=List.ofFn (a s(e.1,e.2) j)) :
    ∃ out : List (Fin n × Fin n),
      execute (StoredEdges.encode Q) (StoredEdges.encode Q) (StoredRecords.encodeWeights w)
        n h t ((indexedRecords id vertices input js es).map encode)=StoredEdges.encode out ∧
      StoredSample.edgeSet out=SampledGreedy.edges (StoredSample.edgeSet Q)
        (fun d => (w d:ℝ)) (t:ℝ) (SampledGreedy.componentEligible Finset.univ F)
        (SampledGreedy.componentHost F) (SampledGreedy.assignmentTape a) h
        (es.map fun e => s(e.1,e.2)).reverse := by
  classical
  let incidence := fun j : ForestComponentIndex F => StoredVertexPairs.typedPairs (vertices j) (vertices j)
  have cover : ∀ e∈es,∀ j∈SampledGreedy.componentEligible Finset.univ F s(e.1,e.2),j∈js := by
    intro e _ j _
    apply List.mem_toFinset.mp
    rw [hall]
    exact Finset.mem_univ _
  have inc : ∀ e∈es,∀ j∈js,j∈SampledGreedy.componentEligible Finset.univ F s(e.1,e.2) ↔
      s(e.1,e.2)∈StoredSample.edgeSet (incidence j) := by
    intro e _ j _
    simpa only [SampledGreedy.componentEligible,forestComponentIndices,Finset.mem_filter,
      Finset.mem_sigma,Finset.mem_univ,true_and,incidence] using
      (StoredVertexPairs.component_incidence (F j.1) j.2 (vertices j) (hv j) e.1 e.2).symm
  obtain ⟨out,he,ho⟩ := StoredPreparedCandidates.execute_assignment Q w hw t
    (SampledGreedy.componentEligible Finset.univ F) (SampledGreedy.componentHost F)
    a h id incidence input js es hj cover inc hh hd
  refine ⟨out,?_,ho⟩
  rw [execute_encoded]
  rw [StoredPreparedCandidates.execute_encoded] at he
  rw [←indexed_prepared id vertices input js es] at he
  simpa only [List.map_map,Function.comp_def] using he
end LightEFTSpanners.StoredComponentCandidates
