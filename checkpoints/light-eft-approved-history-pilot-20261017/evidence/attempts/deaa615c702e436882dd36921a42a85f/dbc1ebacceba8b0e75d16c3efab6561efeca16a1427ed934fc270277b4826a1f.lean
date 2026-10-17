import LightEFTSpanners.ComputableVotingSamples

namespace LightEFTSpanners.SampledGreedy
open SimpleGraph Finset FiniteProbability LightSpanners
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- Transfer a deterministic reached-state correctness/lightness theorem to the
literal finite fresh-tape law. This supplies, rather than assumes, accuracy. -/
theorem polynomial_output_failure_probability (G Q : SimpleGraph V) (w : Sym2 V → ℝ)
    (t B : ℝ) (q f h s : ℕ) (hf : 0<f)
    (hQ : IsFTConnectivityPreserver G Q q) (F : Fin (q+1) → SimpleGraph V)
    (hgood : ∀ tape : Tape V (ForestComponentIndex F),
      AccurateTrace Q.edgeFinset w t f (componentEligible univ F) (componentHost F)
        tape h (input G Q w) →
      IsEFTSpanner G (output G Q w t (componentEligible univ F) (componentHost F) tape h) w t f ∧
      competitiveLightness (output G Q w t (componentEligible univ F) (componentHost F) tape h) Q w≤B) :
    (executionLaw (V:=V) (J:=ForestComponentIndex F) f hf
      (polynomialRepetitions (Fintype.card V) s) (input G Q w)).prob (fun a => ¬(
        IsEFTSpanner G (output G Q w t (componentEligible univ F) (componentHost F)
          (assignmentTape a) h) w t f ∧
        competitiveLightness (output G Q w t (componentEligible univ F) (componentHost F)
          (assignmentTape a) h) Q w≤B)) ≤ ((Fintype.card V:ℝ)^s)⁻¹ := by
  classical
  apply le_trans (Law.prob_mono _ (fun a hbad hacc => hbad (hgood (assignmentTape a) hacc)))
  exact polynomial_inaccurate_probability G Q w t q f h s hf hQ F

end LightEFTSpanners.SampledGreedy
