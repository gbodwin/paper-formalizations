import LightEFTSuppliedForestStage.SuppliedForestGoodEvent
import LightEFTSpanners.ComputableVotingSamples

/-!
Unexecuted draft: no Lean elaboration, compiler, replay or audit in preparation.
The same supplied forest family F, literal executionLaw and assignmentTape are
used throughout. This is not a sampling implementation or a seed/packing
construction; all structural premises on F and Q remain explicit.
-/
namespace LightEFTSpanners.SampledGreedy
open SimpleGraph Finset LightSpanners HostCounting FiniteProbability
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- Failure of the full supplied-forest package is contained in trace
inaccuracy for the very same finite fresh-assignment law. -/
theorem polynomial_supplied_forest_package_failure_probability
    (G Q : SimpleGraph V) (q f h k s : ℕ) (w : Sym2 V → ℝ) (eps : ℝ)
    (hQ : IsFTConnectivityPreserver G Q q)
    (F : Fin (q+1) → SimpleGraph V)
    (hF : ∀ i, F i ≤ Q ∧ (F i).IsAcyclic)
    (hcount : ∀ e ∈ G.edgeFinset \ Q.edgeFinset,
      2*f+h ≤ (componentEligible univ F e).card)
    (hcong : ∀ d : Sym2 V,
      (hosts (univ : Finset (Fin (q+1))) (fun i => (F i).edgeFinset) d).card ≤ 2)
    (hf : 0 < f) (hh : 0 < h) (hk : 0 < k) (heps : 0 < eps)
    (hw : ∀ e, 0 ≤ w e) (hwpos : ∀ e ∈ G.edgeSet, 0 < w e) :
    let t : ℝ := (1+eps)*(2*k-1)
    let B : ℝ := 1+64*(f:ℝ)*extremalLightness (Fintype.card V) (t+1)/h
    (executionLaw (V:=V) (J:=ForestComponentIndex F) f hf
      (polynomialRepetitions (Fintype.card V) s) (input G Q w)).prob (fun a =>
        let H := output G Q w t (componentEligible univ F) (componentHost F)
          (assignmentTape a) h
        ¬(IsEFTSpanner G H w t f ∧
          totalWeight H w ≤ B * totalWeight Q w ∧
          (totalWeight Q w = 0 → totalWeight H w = 0) ∧
          competitiveLightness H Q w ≤ B)) ≤ ((Fintype.card V:ℝ)^s)⁻¹ := by
  classical
  let t : ℝ := (1+eps)*(2*k-1)
  let B : ℝ := 1+64*(f:ℝ)*extremalLightness (Fintype.card V) (t+1)/h
  let μ := executionLaw (V:=V) (J:=ForestComponentIndex F) f hf
    (polynomialRepetitions (Fintype.card V) s) (input G Q w)
  let H := fun a : Assignment V (ForestComponentIndex F)
      (polynomialRepetitions (Fintype.card V) s) =>
    output G Q w t (componentEligible univ F) (componentHost F) (assignmentTape a) h
  change μ.prob (fun a => ¬(IsEFTSpanner G (H a) w t f ∧
    totalWeight (H a) w ≤ B * totalWeight Q w ∧
    (totalWeight Q w = 0 → totalWeight (H a) w = 0) ∧
    competitiveLightness (H a) Q w ≤ B)) ≤ ((Fintype.card V:ℝ)^s)⁻¹
  have hmono :
      μ.prob (fun a => ¬(IsEFTSpanner G (H a) w t f ∧
        totalWeight (H a) w ≤ B * totalWeight Q w ∧
        (totalWeight Q w = 0 → totalWeight (H a) w = 0) ∧
        competitiveLightness (H a) Q w ≤ B)) ≤
      μ.prob (fun a => ¬AccurateTrace Q.edgeFinset w t f
        (componentEligible univ F) (componentHost F) (assignmentTape a) h (input G Q w)) := by
    apply Law.prob_mono
    intro a hbad hacc
    have hgood := voting_good_event_of_supplied_forests G Q hQ.1 q f h k w eps
      F hF hcount hcong hf hh hk heps hw hwpos (assignmentTape a) hacc
    exact hbad hgood
  exact hmono.trans (polynomial_inaccurate_probability G Q w t q f h s hf hQ F)

end LightEFTSpanners.SampledGreedy
