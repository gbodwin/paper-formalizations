import LightEFTSpanners.StoredOutputLaw
import LightEFTSpanners.RandomizedVotingGuarantees

namespace LightEFTSpanners.StoredCandidates
open SimpleGraph LightSpanners SampledGreedy
attribute [local instance] Classical.propDecidable

theorem actual_output_failure_probability {n : ℕ}
    (G Q : SimpleGraph (Fin n)) (seed : List (Fin n × Fin n))
    (w : Sym2 (Fin n) → ℚ) (hw : ∀ e,0≤w e) (t : ℚ) (B : ℝ)
    (q f h s : ℕ) (hf : 0<f) (hQ : IsFTConnectivityPreserver G Q q)
    (F : Fin (q+1) → SimpleGraph (Fin n))
    (js : Sym2 (Fin n) → List (ForestComponentIndex F))
    (bank : SampledGreedy.Assignment (Fin n) (ForestComponentIndex F)
      (SampledGreedy.repetitionCount (Fintype.card (Fin n)) s) → Sym2 (Fin n) → ForestComponentIndex F → StoredHosts.TypedInput n)
    (es : List (Fin n × Fin n))
    (hseed : StoredSample.edgeSet seed=Q.edgeFinset)
    (horder : (es.map fun e => s(e.1,e.2)).reverse=LightEFTSpanners.input G Q (fun d => (w d:ℝ)))
    (hj : ∀ e∈es,(js s(e.1,e.2)).Nodup)
    (he : ∀ e∈es,(js s(e.1,e.2)).toFinset=componentEligible Finset.univ F s(e.1,e.2))
    (hh : ∀ a,∀ e∈es,∀ j∈js s(e.1,e.2),
      componentHost F j=StoredSample.edgeSet (bank a s(e.1,e.2) j).edges)
    (hd : ∀ a,∀ e∈es,∀ j∈js s(e.1,e.2),
      ((bank a s(e.1,e.2) j).draws.map StoredSample.edgeSet)=List.ofFn (a s(e.1,e.2) j))
    (hgood : ∀ tape : SampledGreedy.Tape (Fin n) (ForestComponentIndex F),
      SampledGreedy.AccurateTrace Q.edgeFinset (fun d => (w d:ℝ)) (t:ℝ) f
        (componentEligible Finset.univ F) (componentHost F) tape h
        (LightEFTSpanners.input G Q (fun d => (w d:ℝ))) →
      IsEFTSpanner G (SampledGreedy.output G Q (fun d => (w d:ℝ)) (t:ℝ)
        (componentEligible Finset.univ F) (componentHost F) tape h) (fun d => (w d:ℝ)) (t:ℝ) f ∧
      competitiveLightness (SampledGreedy.output G Q (fun d => (w d:ℝ)) (t:ℝ)
        (componentEligible Finset.univ F) (componentHost F) tape h) Q (fun d => (w d:ℝ))≤B) :
    (SampledGreedy.executionLaw (V:=Fin n) (J:=ForestComponentIndex F) f hf
      (SampledGreedy.repetitionCount (Fintype.card (Fin n)) s) (LightEFTSpanners.input G Q (fun d => (w d:ℝ)))).prob
      (fun a => ¬OutputSatisfies n
        (fun E => IsEFTSpanner G (edgeGraph E) (fun d => (w d:ℝ)) (t:ℝ) f ∧
          competitiveLightness (edgeGraph E) Q (fun d => (w d:ℝ))≤B)
        (execute (StoredEdges.encode seed) (StoredEdges.encode seed) (StoredRecords.encodeWeights w)
          n h ((assignmentRecords w t js (bank a) es).map encode))) ≤ ((n:ℝ)^s)⁻¹ := by
  classical
  have machine := assignment_failure_le seed w hw t (componentEligible Finset.univ F)
    (componentHost F) h js bank es hj he hh hd
    (SampledGreedy.executionLaw (V:=Fin n) (J:=ForestComponentIndex F) f hf
      (SampledGreedy.repetitionCount (Fintype.card (Fin n)) s) (LightEFTSpanners.input G Q (fun d => (w d:ℝ))))
    (fun E => IsEFTSpanner G (edgeGraph E) (fun d => (w d:ℝ)) (t:ℝ) f ∧
      competitiveLightness (edgeGraph E) Q (fun d => (w d:ℝ))≤B)
  apply machine.trans
  simpa only [hseed,horder,SampledGreedy.output,Fintype.card_fin] using
    SampledGreedy.output_failure_probability G Q (fun d => (w d:ℝ)) (t:ℝ) B q f h s hf hQ F hgood
end LightEFTSpanners.StoredCandidates
