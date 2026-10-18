import LightEFTSpanners.StoredForestOutputLaw
import LightEFTSuppliedForestProbabilityStage.PolynomialFailureProbability

/-!
Unelaborated interface draft only. The encoded interpreter output uses the same
forest family, assignment law, candidate list and keyed banks as the mathematical
output. Seed representation, exact candidate order and draw correspondence remain
explicit hypotheses. No sampling, serialization-cost or runtime claim is made.
-/
namespace LightEFTSpanners.StoredForestCandidates
open SimpleGraph Finset LightSpanners SampledGreedy HostCounting
open StoredCandidates (OutputSatisfies)
attribute [local instance] Classical.propDecidable

/-- Transfer the full supplied-forest package to the encoded interpreter output
under the exact existing assignment law and explicit representation hypotheses. -/
theorem polynomial_actual_supplied_forest_package_failure_probability {n : ℕ}
    (G Q : SimpleGraph (Fin n)) (seed : List (Fin n × Fin n))
    (w : Sym2 (Fin n) → ℚ) (q f h k s : ℕ) (eps : ℚ)
    (hQ : IsFTConnectivityPreserver G Q q)
    (edges : Fin (q+1) → List (Fin n × Fin n))
    (hF : ∀ i, StoredForestHosts.family edges i ≤ Q ∧
      (StoredForestHosts.family edges i).IsAcyclic)
    (hcount : ∀ e ∈ G.edgeFinset \ Q.edgeFinset,
      2*f+h ≤ (componentEligible univ (StoredForestHosts.family edges) e).card)
    (hcong : ∀ d : Sym2 (Fin n),
      (hosts (univ : Finset (Fin (q+1)))
        (fun i => (StoredForestHosts.family edges i).edgeFinset) d).card ≤ 2)
    (hf : 0 < f) (hh : 0 < h) (hk : 0 < k) (heps : 0 < eps)
    (hw : ∀ e, 0 ≤ w e) (hwpos : ∀ e ∈ G.edgeSet, 0 < w e)
    (banks : Assignment (Fin n) (ForestComponentIndex (StoredForestHosts.family edges))
      (polynomialRepetitions (Fintype.card (Fin n)) s) →
      Sym2 (Fin n) → StoredDrawLookup.TypedBank n)
    (es : List (Fin n × Fin n))
    (hseed : StoredSample.edgeSet seed = Q.edgeFinset)
    (horder : (es.map fun e => s(e.1,e.2)).reverse =
      LightEFTSpanners.input G Q (fun d => (w d:ℝ)))
    (hd : ∀ a, ∀ e ∈ es, ∀ j ∈ StoredForestHosts.indices edges,
      ((hostInput edges (banks a) s(e.1,e.2) j).draws.map StoredSample.edgeSet) =
        List.ofFn (a s(e.1,e.2) j)) :
    let t : ℝ := (1+(eps:ℝ))*(2*k-1)
    let B : ℝ := 1+64*(f:ℝ)*extremalLightness n (t+1)/h
    (executionLaw (V:=Fin n) (J:=ForestComponentIndex (StoredForestHosts.family edges)) f hf
      (polynomialRepetitions (Fintype.card (Fin n)) s)
      (LightEFTSpanners.input G Q (fun d => (w d:ℝ)))).prob (fun a =>
        ¬OutputSatisfies n
          (fun E => IsEFTSpanner G (edgeGraph E) (fun d => (w d:ℝ)) t f ∧
            totalWeight (edgeGraph E) (fun d => (w d:ℝ)) ≤
              B * totalWeight Q (fun d => (w d:ℝ)) ∧
            (totalWeight Q (fun d => (w d:ℝ)) = 0 →
              totalWeight (edgeGraph E) (fun d => (w d:ℝ)) = 0) ∧
            competitiveLightness (edgeGraph E) Q (fun d => (w d:ℝ)) ≤ B)
          (execute n h ((List.ofFn edges).map StoredEdges.encode)
            (StoredEdges.encode seed) (StoredEdges.encode seed)
            (StoredRecords.encodeWeights w) ((1+eps)*(2*(k:ℚ)-1))
            ((rawInputs (banks a) es).map StoredForestBank.encode))) ≤ ((n:ℝ)^s)⁻¹ := by
  classical
  let t : ℝ := (1+(eps:ℝ))*(2*k-1)
  let B : ℝ := 1+64*(f:ℝ)*extremalLightness n (t+1)/h
  have ht : (((1+eps)*(2*(k:ℚ)-1):ℚ):ℝ) = t := by
    dsimp [t]
    push_cast
    rfl
  have hwR : ∀ e, 0 ≤ (w e:ℝ) := fun e => by exact_mod_cast hw e
  have hwposR : ∀ e ∈ G.edgeSet, 0 < (w e:ℝ) :=
    fun e he => by exact_mod_cast hwpos e he
  have hepsR : 0 < (eps:ℝ) := by exact_mod_cast heps
  have machine := assignment_failure_le edges seed w hw ((1+eps)*(2*(k:ℚ)-1)) h banks es hd
    (executionLaw (V:=Fin n) (J:=ForestComponentIndex (StoredForestHosts.family edges)) f hf
      (polynomialRepetitions (Fintype.card (Fin n)) s)
      (LightEFTSpanners.input G Q (fun d => (w d:ℝ))))
    (fun E => IsEFTSpanner G (edgeGraph E) (fun d => (w d:ℝ)) t f ∧
      totalWeight (edgeGraph E) (fun d => (w d:ℝ)) ≤
        B * totalWeight Q (fun d => (w d:ℝ)) ∧
      (totalWeight Q (fun d => (w d:ℝ)) = 0 →
        totalWeight (edgeGraph E) (fun d => (w d:ℝ)) = 0) ∧
      competitiveLightness (edgeGraph E) Q (fun d => (w d:ℝ)) ≤ B)
  apply machine.trans
  simpa only [hseed, horder, ht, SampledGreedy.output, Fintype.card_fin] using
    SampledGreedy.polynomial_supplied_forest_package_failure_probability G Q q f h k s
      (fun d => (w d:ℝ)) (eps:ℝ) hQ (StoredForestHosts.family edges)
      hF hcount hcong hf hh hk hepsR hwR hwposR

end LightEFTSpanners.StoredForestCandidates
