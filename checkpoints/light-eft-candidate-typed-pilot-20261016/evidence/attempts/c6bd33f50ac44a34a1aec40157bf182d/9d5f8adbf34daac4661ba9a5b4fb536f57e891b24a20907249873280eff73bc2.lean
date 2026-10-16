import LightEFTSpanners.PreparedProbabilityGuarantee

namespace LightEFTSpanners.StoredPreparedCandidates
open SimpleGraph LightSpanners SampledGreedy
open StoredCandidatePreparation
open StoredCandidates (OutputSatisfies)
attribute [local instance] Classical.propDecidable

/-- Internally chosen minimum seed and forest hosts, the original finite fresh
assignment law, and the actual stored interpreter's returned graph. The interpreter constructs budgets and eligible hosts from represented original
incidence catalogues; raw catalogue construction and random sampling remain separate. -/
theorem exists_prepared_optimum_high_probability {n : ℕ}
    (G : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℚ)
    (q f h k s : ℕ) (eps : ℚ) (hbudget : 2*f+h≤q+1)
    (hf : 0<f) (hh : 0<h) (hk : 0<k) (heps : 0<eps)
    (hw : ∀ e,0≤w e) (hwpos : ∀ e∈G.edgeSet,0<w e) :
    ∃ Q : SimpleGraph (Fin n),IsMinimumFTPreserver G Q (fun d => (w d:ℝ)) q ∧
      ∃ F : Fin (q+1) → SimpleGraph (Fin n),
        (∀ i,F i≤Q ∧ (F i).IsAcyclic) ∧
        ∀ (seed : List (Fin n × Fin n))
          (id : ForestComponentIndex F → ℕ)
          (incidence : ForestComponentIndex F → List (Fin n × Fin n))
          (js : List (ForestComponentIndex F))
          (bank : Assignment (Fin n) (ForestComponentIndex F) (repetitionCount (Fintype.card (Fin n)) s) →
            Sym2 (Fin n) → ForestComponentIndex F → StoredHosts.TypedInput n)
          (es : List (Fin n × Fin n)),
          StoredSample.edgeSet seed=Q.edgeFinset →
          (es.map fun e => s(e.1,e.2)).reverse=LightEFTSpanners.input G Q (fun d => (w d:ℝ)) →
          js.Nodup →
          (∀ e∈es,∀ j∈componentEligible Finset.univ F s(e.1,e.2),j∈js) →
          (∀ e∈es,∀ j∈js,j∈componentEligible Finset.univ F s(e.1,e.2) ↔
            s(e.1,e.2)∈StoredSample.edgeSet (incidence j)) →
          (∀ a,∀ e∈es,∀ j∈js,
            componentHost F j=StoredSample.edgeSet (bank a s(e.1,e.2) j).edges) →
          (∀ a,∀ e∈es,∀ j∈js,
            ((bank a s(e.1,e.2) j).draws.map StoredSample.edgeSet)=List.ofFn (a s(e.1,e.2) j)) →
          (executionLaw (V:=Fin n) (J:=ForestComponentIndex F) f hf
            (repetitionCount (Fintype.card (Fin n)) s) (LightEFTSpanners.input G Q (fun d => (w d:ℝ)))).prob
            (fun a => ¬OutputSatisfies n
              (fun E => IsEFTSpanner G (edgeGraph E) (fun d => (w d:ℝ))
                  ((1+(eps:ℝ))*(2*k-1)) f ∧
                competitiveLightness (edgeGraph E) Q (fun d => (w d:ℝ))≤
                  1+64*(f:ℝ)*extremalLightness n ((1+(eps:ℝ))*(2*k-1)+1)/h)
              (execute (StoredEdges.encode seed) (StoredEdges.encode seed) (StoredRecords.encodeWeights w)
                n h ((1+eps)*(2*(k:ℚ)-1)) ((indexedRecords id incidence (bank a) js es).map encode))) ≤
            ((n:ℝ)^s)⁻¹ := by
  classical
  have hwR : ∀ e,0≤(w e:ℝ) := fun e => by exact_mod_cast hw e
  have hpR : ∀ e∈G.edgeSet,0<(w e:ℝ) := fun e he => by exact_mod_cast hwpos e he
  obtain ⟨Q,hQ,F,hF,hgood⟩ := exists_optimum_voting_good_event G (fun d => (w d:ℝ))
    q f h k (eps:ℝ) hbudget hf hh hk (by exact_mod_cast heps) hwR hpR
  refine ⟨Q,hQ,F,hF,?_⟩
  intro seed id incidence js bank es hseed horder hj cover inc hhost hdraw
  have ht : (((1+eps)*(2*(k:ℚ)-1):ℚ):ℝ)=(1+(eps:ℝ))*(2*k-1) := by push_cast; rfl
  have hg := actual_output_failure_probability G Q seed w hw ((1+eps)*(2*(k:ℚ)-1))
    (1+64*(f:ℝ)*extremalLightness n ((1+(eps:ℝ))*(2*k-1)+1)/h)
    q f h s hf hQ.1 F id incidence js bank es hseed horder hj cover inc hhost hdraw
    (by simpa only [ht,Fintype.card_fin] using hgood)
  simpa only [ht] using hg
end LightEFTSpanners.StoredPreparedCandidates
