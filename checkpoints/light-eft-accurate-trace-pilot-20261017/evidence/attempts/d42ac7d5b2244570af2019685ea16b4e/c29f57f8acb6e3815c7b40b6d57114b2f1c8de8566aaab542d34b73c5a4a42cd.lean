import LightEFTSpanners.StoredOriginalGraphExecutable
import LightEFTSpanners.StoredOriginalOrderRepresentation

namespace LightEFTSpanners.StoredOriginalGraphCaller
open StoredForestCandidates
attribute [local instance] Classical.propDecidable

theorem execute_original_graph {n : ℕ} (G Q : SimpleGraph (Fin n)) (h : ℕ)
    (fs : List (List (Fin n × Fin n))) (E : List (Fin n × Fin n)) (w : Sym2 (Fin n) → ℚ)
    (banks : Sym2 (Fin n) → StoredDrawLookup.TypedBank n) (t : ℚ) :
    execute n h (fs.map StoredEdges.encode) (StoredEdges.encode (graphEdges Q)) (StoredEdges.encode E)
      (StoredEdges.encode (pairList G.edgeFinset.toList))
      (StoredOriginalWeightLookup.encode (StoredOriginalWeightLookup.originalBank w))
      (StoredCandidateDrawLookup.encode (StoredCandidateDrawLookup.originalBank banks)) t=
    StoredWeightedForestCandidates.execute n h (fs.map StoredEdges.encode) (StoredEdges.encode (graphEdges Q))
      (StoredEdges.encode E) (StoredOriginalWeightLookup.encode (StoredOriginalWeightLookup.originalBank w)) t
      ((rawInputs banks (pairList (LightEFTSpanners.input G Q (fun d => (w d:ℝ))).reverse)).map StoredForestBank.encode) := by
  rw [execute_composed,StoredSortedCandidateInput.execute_original_order]
  simp only [rawInputs,pairList,List.map_reverse]
end LightEFTSpanners.StoredOriginalGraphCaller
