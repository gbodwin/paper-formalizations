import LightEFTSpanners.StoredOriginalGraphOutput
import LightEFTSpanners.ComputableForestGuarantee
import LightEFTSpanners.StoredOriginalWeightedOutput

namespace LightEFTSpanners.StoredForestCandidates
open SimpleGraph LightSpanners SampledGreedy
open StoredCandidates (OutputSatisfies)
attribute [local instance] Classical.propDecidable

/-- The actual program sorts the original edge list, filters the seed, reads the original draw bank and constructs the matrix before the forest interpreter.
Minimum seed/forest choice and finite-set orientation are mathematical choices;
the polynomial repetition count avoids real-log evaluation; sampling and physical input preparation remain separate. -/
theorem exists_computable_graph_forest_high_probability {n : ℕ}
    (G : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℚ)
    (q f h k s : ℕ) (eps : ℚ) (hbudget : 2*f+h≤q+1)
    (hf : 0<f) (hh : 0<h) (hk : 0<k) (heps : 0<eps)
    (hw : ∀ e,0≤w e) (hwpos : ∀ e∈G.edgeSet,0<w e) :
    ∃ Q : SimpleGraph (Fin n),IsMinimumFTPreserver G Q (fun d => (w d:ℝ)) q ∧
      ∃ edges : Fin (q+1) → List (Fin n × Fin n),
        (∀ i,StoredForestHosts.family edges i≤Q ∧ (StoredForestHosts.family edges i).IsAcyclic) ∧
        (executionLaw (V:=Fin n) (J:=ForestComponentIndex (StoredForestHosts.family edges)) f hf
          (polynomialRepetitions (Fintype.card (Fin n)) s) (LightEFTSpanners.input G Q (fun d => (w d:ℝ)))).prob
          (fun a => ¬OutputSatisfies n
            (fun E => IsEFTSpanner G (edgeGraph E) (fun d => (w d:ℝ)) ((1+(eps:ℝ))*(2*k-1)) f ∧
              competitiveLightness (edgeGraph E) Q (fun d => (w d:ℝ))≤
                1+64*(f:ℝ)*extremalLightness n ((1+(eps:ℝ))*(2*k-1)+1)/h)
            (StoredOriginalGraphCaller.execute n h ((List.ofFn edges).map StoredEdges.encode)
              (StoredEdges.encode (graphEdges Q)) (StoredEdges.encode (graphEdges Q))
              (StoredEdges.encode (pairList G.edgeFinset.toList))
              (StoredOriginalWeightLookup.encode (StoredOriginalWeightLookup.originalBank w))
              (StoredCandidateDrawLookup.encode (StoredCandidateDrawLookup.originalBank (assignmentBank edges a)))
              ((1+eps)*(2*(k:ℚ)-1)))) ≤
          ((n:ℝ)^s)⁻¹ := by
  obtain ⟨Q,hQ,edges,hF,guarantee⟩ := exists_polynomial_forest_optimum_high_probability G w q f h k s eps
    hbudget hf hh hk heps hw hwpos
  refine ⟨Q,hQ,edges,hF,?_⟩
  have hg := guarantee (graphEdges Q) (assignmentBank edges)
    (pairList (LightEFTSpanners.input G Q (fun d => (w d:ℝ))).reverse)
    (graphEdges_edgeSet Q) (by rw [pairList_represents,List.reverse_reverse])
    (fun a e _ j _ => assignmentBank_represents edges a s(e.1,e.2) j)
  simpa only [StoredOriginalGraphCaller.execute_original_graph,
    StoredWeightedForestCandidates.execute_original_weights] using hg
end LightEFTSpanners.StoredForestCandidates
