import LightEFTJointFlagSamplingStage.JointAssignmentLaw
import LightEFTActualSuppliedForestProbabilityStage.PolynomialActualFailureProbability
import LightEFTSpanners.StoredCanonicalAssignmentOutput

/-!
Source-only staged corollary; not yet elaborated or kernel checked.
The canonical seed, endpoint order and assignment banks below are mathematical
representations. No paid sampling, serialization, seed construction, packing or
runtime claim is made.
-/
namespace LightEFTSpanners.StoredForestCandidates
open SimpleGraph Finset LightSpanners SampledGreedy HostCounting
open StoredCandidates (OutputSatisfies)
attribute [local instance] Classical.propDecidable

/-- The canonical encoded interpreter preserves the entire four-part supplied-
forest output package with polynomial failure probability under the literal
joint flag law. No representation, independence, coupling, accuracy or nodup
hypothesis is supplied by the caller. -/
theorem polynomial_canonical_joint_flags_actual_output_failure_probability {n : ℕ}
    (G Q : SimpleGraph (Fin n))
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
    (hw : ∀ e, 0 ≤ w e) (hwpos : ∀ e ∈ G.edgeSet, 0 < w e) :
    let l := LightEFTSpanners.input G Q (fun d => (w d:ℝ))
    let m := polynomialRepetitions (Fintype.card (Fin n)) s
    let t : ℝ := (1+(eps:ℝ))*(2*k-1)
    let B : ℝ := 1+64*(f:ℝ)*extremalLightness n (t+1)/h
    (JointFlagSampling.jointSourceLaw
      (J:=ForestComponentIndex (StoredForestHosts.family edges)) n f m hf l).prob
      (fun bits => ¬OutputSatisfies n
        (fun E => IsEFTSpanner G (edgeGraph E) (fun d => (w d:ℝ)) t f ∧
          totalWeight (edgeGraph E) (fun d => (w d:ℝ)) ≤
            B * totalWeight Q (fun d => (w d:ℝ)) ∧
          (totalWeight Q (fun d => (w d:ℝ)) = 0 →
            totalWeight (edgeGraph E) (fun d => (w d:ℝ)) = 0) ∧
          competitiveLightness (edgeGraph E) Q (fun d => (w d:ℝ)) ≤ B)
        (execute n h ((List.ofFn edges).map StoredEdges.encode)
          (StoredEdges.encode (graphEdges Q)) (StoredEdges.encode (graphEdges Q))
          (StoredRecords.encodeWeights w) ((1+eps)*(2*(k:ℚ)-1))
          ((rawInputs (assignmentBank edges (JointFlagSampling.decodeAssignment l bits))
            (pairList (List.reverse l))).map StoredForestBank.encode))) ≤ ((n:ℝ)^s)⁻¹ := by
  classical
  let l := LightEFTSpanners.input G Q (fun d => (w d:ℝ))
  have bound := polynomial_actual_supplied_forest_package_failure_probability
    G Q (graphEdges Q) w q f h k s eps hQ edges hF hcount hcong
    hf hh hk heps hw hwpos (assignmentBank edges) (pairList (List.reverse l))
    (graphEdges_edgeSet Q) (by rw [pairList_represents, List.reverse_reverse])
    (fun a e _ j _ => assignmentBank_represents edges a s(e.1,e.2) j)
  dsimp only at bound ⊢
  rw [← JointFlagSampling.decoded_assignment_probability n f
    (polynomialRepetitions (Fintype.card (Fin n)) s) hf l] at bound
  exact bound

end LightEFTSpanners.StoredForestCandidates
