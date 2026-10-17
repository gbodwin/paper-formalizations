import LightEFTSpanners.StoredForestOutputLaw
import LightEFTSpanners.RandomizedVotingGuarantees

namespace LightEFTSpanners.StoredForestCandidates
open SimpleGraph LightSpanners SampledGreedy
open StoredCandidates (OutputSatisfies)
attribute [local instance] Classical.propDecidable

theorem actual_output_failure_probability {n : ℕ}
    (G Q : SimpleGraph (Fin n)) (seed : List (Fin n × Fin n))
    (w : Sym2 (Fin n) → ℚ) (hw : ∀ e,0≤w e) (t : ℚ) (B : ℝ)
    (q f h s : ℕ) (hf : 0<f) (hQ : IsFTConnectivityPreserver G Q q)
    (edges : Fin (q+1) → List (Fin n × Fin n))
    (banks : SampledGreedy.Assignment (Fin n) (ForestComponentIndex (StoredForestHosts.family edges))
      (SampledGreedy.repetitionCount (Fintype.card (Fin n)) s) → Sym2 (Fin n) → StoredDrawLookup.TypedBank n)
    (es : List (Fin n × Fin n))
    (hseed : StoredSample.edgeSet seed=Q.edgeFinset)
    (horder : (es.map fun e => s(e.1,e.2)).reverse=LightEFTSpanners.input G Q (fun d => (w d:ℝ)))
    (hd : ∀ a,∀ e∈es,∀ j∈StoredForestHosts.indices edges,
      ((hostInput edges (banks a) s(e.1,e.2) j).draws.map StoredSample.edgeSet)=List.ofFn (a s(e.1,e.2) j))
    (hgood : ∀ tape : SampledGreedy.Tape (Fin n) (ForestComponentIndex (StoredForestHosts.family edges)),
      SampledGreedy.AccurateTrace Q.edgeFinset (fun d => (w d:ℝ)) (t:ℝ) f
        (componentEligible Finset.univ (StoredForestHosts.family edges)) (componentHost (StoredForestHosts.family edges)) tape h
        (LightEFTSpanners.input G Q (fun d => (w d:ℝ))) →
      IsEFTSpanner G (SampledGreedy.output G Q (fun d => (w d:ℝ)) (t:ℝ)
        (componentEligible Finset.univ (StoredForestHosts.family edges)) (componentHost (StoredForestHosts.family edges)) tape h) (fun d => (w d:ℝ)) (t:ℝ) f ∧
      competitiveLightness (SampledGreedy.output G Q (fun d => (w d:ℝ)) (t:ℝ)
        (componentEligible Finset.univ (StoredForestHosts.family edges)) (componentHost (StoredForestHosts.family edges)) tape h) Q (fun d => (w d:ℝ))≤B) :
    (SampledGreedy.executionLaw (V:=Fin n) (J:=ForestComponentIndex (StoredForestHosts.family edges)) f hf
      (SampledGreedy.repetitionCount (Fintype.card (Fin n)) s) (LightEFTSpanners.input G Q (fun d => (w d:ℝ)))).prob
      (fun a => ¬OutputSatisfies n
        (fun E => IsEFTSpanner G (edgeGraph E) (fun d => (w d:ℝ)) (t:ℝ) f ∧
          competitiveLightness (edgeGraph E) Q (fun d => (w d:ℝ))≤B)
        (execute n h ((List.ofFn edges).map StoredEdges.encode) (StoredEdges.encode seed) (StoredEdges.encode seed)
          (StoredRecords.encodeWeights w) t ((rawInputs (banks a) es).map StoredForestBank.encode))) ≤ ((n:ℝ)^s)⁻¹ := by
  classical
  have machine := assignment_failure_le edges seed w hw t h banks es hd
    (SampledGreedy.executionLaw (V:=Fin n) (J:=ForestComponentIndex (StoredForestHosts.family edges)) f hf
      (SampledGreedy.repetitionCount (Fintype.card (Fin n)) s) (LightEFTSpanners.input G Q (fun d => (w d:ℝ))))
    (fun E => IsEFTSpanner G (edgeGraph E) (fun d => (w d:ℝ)) (t:ℝ) f ∧
      competitiveLightness (edgeGraph E) Q (fun d => (w d:ℝ))≤B)
  apply machine.trans
  simpa only [hseed,horder,SampledGreedy.output,Fintype.card_fin] using
    SampledGreedy.output_failure_probability G Q (fun d => (w d:ℝ)) (t:ℝ) B q f h s hf hQ (StoredForestHosts.family edges) hgood
end LightEFTSpanners.StoredForestCandidates
