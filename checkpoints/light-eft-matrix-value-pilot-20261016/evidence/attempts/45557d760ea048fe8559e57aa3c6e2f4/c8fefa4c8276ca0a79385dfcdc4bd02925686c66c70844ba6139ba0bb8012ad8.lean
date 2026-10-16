import LightEFTSpanners.StoredForestProbabilityGuarantee
import LightEFTSpanners.StoredForestRepresentation

namespace LightEFTSpanners.StoredForestCandidates
open SimpleGraph LightSpanners SampledGreedy
open StoredCandidates (OutputSatisfies)
attribute [local instance] Classical.propDecidable

/-- The actual interpreter constructs all component/host/eligible records and
candidate budgets from the original forest and keyed-draw lists. Minimum seed
and forest choice remain mathematical; this is not a sampler or bit-runtime claim. -/
theorem exists_forest_optimum_high_probability {n : ℕ}
    (G : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℚ)
    (q f h k s : ℕ) (eps : ℚ) (hbudget : 2*f+h≤q+1)
    (hf : 0<f) (hh : 0<h) (hk : 0<k) (heps : 0<eps)
    (hw : ∀ e,0≤w e) (hwpos : ∀ e∈G.edgeSet,0<w e) :
    ∃ Q : SimpleGraph (Fin n),IsMinimumFTPreserver G Q (fun d => (w d:ℝ)) q ∧
      ∃ edges : Fin (q+1) → List (Fin n × Fin n),
        (∀ i,StoredForestHosts.family edges i≤Q ∧ (StoredForestHosts.family edges i).IsAcyclic) ∧
        ∀ (seed : List (Fin n × Fin n))
          (banks : Assignment (Fin n) (ForestComponentIndex (StoredForestHosts.family edges))
            (repetitionCount (Fintype.card (Fin n)) s) → Sym2 (Fin n) → StoredDrawLookup.TypedBank n)
          (es : List (Fin n × Fin n)),
          StoredSample.edgeSet seed=Q.edgeFinset →
          (es.map fun e => s(e.1,e.2)).reverse=LightEFTSpanners.input G Q (fun d => (w d:ℝ)) →
          (∀ a,∀ e∈es,∀ j∈StoredForestHosts.indices edges,
            ((hostInput edges (banks a) s(e.1,e.2) j).draws.map StoredSample.edgeSet)=List.ofFn (a s(e.1,e.2) j)) →
          (executionLaw (V:=Fin n) (J:=ForestComponentIndex (StoredForestHosts.family edges)) f hf
            (repetitionCount (Fintype.card (Fin n)) s) (LightEFTSpanners.input G Q (fun d => (w d:ℝ)))).prob
            (fun a => ¬OutputSatisfies n
              (fun E => IsEFTSpanner G (edgeGraph E) (fun d => (w d:ℝ))
                  ((1+(eps:ℝ))*(2*k-1)) f ∧
                competitiveLightness (edgeGraph E) Q (fun d => (w d:ℝ))≤
                  1+64*(f:ℝ)*extremalLightness n ((1+(eps:ℝ))*(2*k-1)+1)/h)
              (execute n h ((List.ofFn edges).map StoredEdges.encode) (StoredEdges.encode seed) (StoredEdges.encode seed)
                (StoredRecords.encodeWeights w) ((1+eps)*(2*(k:ℚ)-1))
                ((rawInputs (banks a) es).map StoredForestBank.encode))) ≤
            ((n:ℝ)^s)⁻¹ := by
  classical
  have hwR : ∀ e,0≤(w e:ℝ) := fun e => by exact_mod_cast hw e
  have hpR : ∀ e∈G.edgeSet,0<(w e:ℝ) := fun e he => by exact_mod_cast hwpos e he
  obtain ⟨Q,hQ,F,hF,hgood⟩ := exists_optimum_voting_good_event G (fun d => (w d:ℝ))
    q f h k (eps:ℝ) hbudget hf hh hk (by exact_mod_cast heps) hwR hpR
  let edges : Fin (q+1) → List (Fin n × Fin n) := fun i => graphEdges (F i)
  have hrep : StoredForestHosts.family edges=F := represented_family F
  rw [←hrep] at hF hgood
  refine ⟨Q,hQ,edges,hF,?_⟩
  intro seed banks es hseed horder hdraw
  have ht : (((1+eps)*(2*(k:ℚ)-1):ℚ):ℝ)=(1+(eps:ℝ))*(2*k-1) := by push_cast; rfl
  have hg := actual_output_failure_probability G Q seed w hw ((1+eps)*(2*(k:ℚ)-1))
    (1+64*(f:ℝ)*extremalLightness n ((1+(eps:ℝ))*(2*k-1)+1)/h)
    q f h s hf hQ.1 edges banks es hseed horder hdraw
    (by simpa only [ht,Fintype.card_fin] using hgood)
  simpa only [ht] using hg
end LightEFTSpanners.StoredForestCandidates
