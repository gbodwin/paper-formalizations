import LightEFTSpanners.StoredAssignmentDrawBank
import LightEFTSpanners.StoredForestGreedyGuarantee

namespace LightEFTSpanners.StoredForestCandidates
open StoredCandidates (OutputSatisfies)
attribute [local instance] Classical.propDecidable

theorem execute_canonical_assignment {n m q : ℕ} (edges : Fin (q+1) → List (Fin n × Fin n))
    (Q : List (Fin n × Fin n)) (w : Sym2 (Fin n) → ℚ) (hw : ∀ e,0≤w e) (t : ℚ)
    (a : SampledGreedy.Assignment (Fin n) (ForestComponentIndex (StoredForestHosts.family edges)) m)
    (h : ℕ) (es : List (Fin n × Fin n)) :
    ∃ out : List (Fin n × Fin n),
      execute n h ((List.ofFn edges).map StoredEdges.encode) (StoredEdges.encode Q) (StoredEdges.encode Q)
        (StoredRecords.encodeWeights w) t ((rawInputs (assignmentBank edges a) es).map StoredForestBank.encode)=
        StoredEdges.encode out ∧
      StoredSample.edgeSet out=SampledGreedy.edges (StoredSample.edgeSet Q) (fun d => (w d:ℝ)) (t:ℝ)
        (SampledGreedy.componentEligible Finset.univ (StoredForestHosts.family edges))
        (SampledGreedy.componentHost (StoredForestHosts.family edges)) (SampledGreedy.assignmentTape a) h
        (es.map fun e => s(e.1,e.2)).reverse :=
  execute_forest_assignment edges Q w hw t a h (assignmentBank edges a) es
    (fun e _ j _ => assignmentBank_represents edges a s(e.1,e.2) j)

noncomputable def pairList {n : ℕ} (es : List (Sym2 (Fin n))) : List (Fin n × Fin n) :=
  es.map fun e => e.out

theorem pairList_represents {n : ℕ} (es : List (Sym2 (Fin n))) :
    (pairList es).map (fun e => s(e.1,e.2))=es := by
  unfold pairList
  rw [List.map_map]
  conv_rhs => rw [←List.map_id es]
  apply List.map_congr_left
  intro e _
  exact e.out_eq

theorem graphEdges_edgeSet {n : ℕ} (G : SimpleGraph (Fin n)) :
    StoredSample.edgeSet (graphEdges G)=G.edgeFinset := by
  ext e
  induction e using Sym2.inductionOn with
  | _ u v => simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using graphEdges_mem_set G u v
end LightEFTSpanners.StoredForestCandidates
