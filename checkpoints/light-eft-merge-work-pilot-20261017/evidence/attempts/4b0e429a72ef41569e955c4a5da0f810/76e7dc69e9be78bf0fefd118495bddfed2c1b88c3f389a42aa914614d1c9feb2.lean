import LightEFTSpanners.StoredForestAssignment
import LightEFTSpanners.StoredOutputLaw

namespace LightEFTSpanners.StoredForestCandidates
open StoredCandidates (OutputSatisfies)
attribute [local instance] Classical.propDecidable

theorem assignment_failure_le {n m q : ℕ} (edges : Fin (q+1) → List (Fin n × Fin n))
    (Q : List (Fin n × Fin n)) (w : Sym2 (Fin n) → ℚ) (hw : ∀ e,0≤w e) (t : ℚ)
    (h : ℕ)
    (banks : SampledGreedy.Assignment (Fin n) (ForestComponentIndex (StoredForestHosts.family edges)) m →
      Sym2 (Fin n) → StoredDrawLookup.TypedBank n) (es : List (Fin n × Fin n))
    (hd : ∀ a,∀ e∈es,∀ j∈StoredForestHosts.indices edges,
      ((hostInput edges (banks a) s(e.1,e.2) j).draws.map StoredSample.edgeSet)=List.ofFn (a s(e.1,e.2) j))
    (law : FiniteProbability.Law (SampledGreedy.Assignment (Fin n)
      (ForestComponentIndex (StoredForestHosts.family edges)) m))
    (P : Finset (Sym2 (Fin n)) → Prop) :
    law.prob (fun a => ¬OutputSatisfies n P
      (execute n h ((List.ofFn edges).map StoredEdges.encode) (StoredEdges.encode Q) (StoredEdges.encode Q)
        (StoredRecords.encodeWeights w) t ((rawInputs (banks a) es).map StoredForestBank.encode))) ≤
    law.prob (fun a => ¬P (SampledGreedy.edges (StoredSample.edgeSet Q)
      (fun d => (w d:ℝ)) (t:ℝ)
      (SampledGreedy.componentEligible Finset.univ (StoredForestHosts.family edges))
      (SampledGreedy.componentHost (StoredForestHosts.family edges)) (SampledGreedy.assignmentTape a) h
      (es.map fun e => s(e.1,e.2)).reverse)) := by
  apply FiniteProbability.Law.prob_mono
  intro a hbad hgood
  obtain ⟨out,run,he⟩ := execute_forest_assignment edges Q w hw t a h (banks a) es (hd a)
  exact hbad ⟨out,run,he.symm ▸ hgood⟩
end LightEFTSpanners.StoredForestCandidates
