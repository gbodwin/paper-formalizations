import LightEFTSpanners.LogarithmicVotingSamples

namespace LightEFTSpanners.SampledGreedy
open SimpleGraph Finset FiniteProbability LightSpanners
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- Transfer a deterministic reached-state correctness/lightness theorem to the
literal finite fresh-tape law. This supplies, rather than assumes, accuracy. -/
theorem output_failure_probability (G Q : SimpleGraph V) (w : Sym2 V → ℝ)
    (t B : ℝ) (q f h s : ℕ) (hf : 0<f)
    (hQ : IsFTConnectivityPreserver G Q q) (F : Fin (q+1) → SimpleGraph V)
    (hgood : ∀ tape : Tape V (ForestComponentIndex F),
      AccurateTrace Q.edgeFinset w t f (componentEligible univ F) (componentHost F)
        tape h (input G Q w) →
      IsEFTSpanner G (output G Q w t (componentEligible univ F) (componentHost F) tape h) w t f ∧
      competitiveLightness (output G Q w t (componentEligible univ F) (componentHost F) tape h) Q w≤B) :
    (executionLaw (V:=V) (J:=ForestComponentIndex F) f hf
      (repetitionCount (Fintype.card V) s) (input G Q w)).prob (fun a => ¬(
        IsEFTSpanner G (output G Q w t (componentEligible univ F) (componentHost F)
          (assignmentTape a) h) w t f ∧
        competitiveLightness (output G Q w t (componentEligible univ F) (componentHost F)
          (assignmentTape a) h) Q w≤B)) ≤ ((Fintype.card V:ℝ)^s)⁻¹ := by
  classical
  apply le_trans (Law.prob_mono _ (fun a hbad hacc => hbad (hgood (assignmentTape a) hacc)))
  exact constructed_inaccurate_probability G Q w t q f h s hf hQ F

/-- Corrected Algorithm2, with genuine fresh independent samples and the
adaptive union bound. The same output is both fault tolerant and light with
failure probability at most n^(-s), using ceil(32(s+5)log n)+1 draws per test.
The minimum seed/packing construction is still finite mathematical choice;
no executable or polynomial running-time claim is made here. -/
theorem exists_algorithm_two_high_probability (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (f k s : ℕ) (eps : ℝ) (hf : 0<f) (hk : 0<k) (heps : 0<eps)
    (hw : ∀ e,0≤w e) (hwpos : ∀ e∈G.edgeSet,0<w e) :
    ∃ Q : SimpleGraph V,IsMinimumFTPreserver G Q w (2*f) ∧
      ∃ F : Fin (2*f+1) → SimpleGraph V,
        (∀ i,F i≤Q ∧ (F i).IsAcyclic) ∧
        (executionLaw (V:=V) (J:=ForestComponentIndex F) f hf
          (repetitionCount (Fintype.card V) s) (input G Q w)).prob (fun a => ¬(
            IsEFTSpanner G (output G Q w ((1+eps)*(2*k-1))
              (componentEligible univ F) (componentHost F) (assignmentTape a) 1) w ((1+eps)*(2*k-1)) f ∧
            competitiveLightness (output G Q w ((1+eps)*(2*k-1))
              (componentEligible univ F) (componentHost F) (assignmentTape a) 1) Q w≤
              1+64*(f:ℝ)*extremalLightness (Fintype.card V) ((1+eps)*(2*k-1)+1))) ≤
          ((Fintype.card V:ℝ)^s)⁻¹ := by
  classical
  obtain ⟨Q,hQ,F,hF,hgood⟩ := exists_algorithm_two_good_event G w f k eps hf hk heps hw hwpos
  exact ⟨Q,hQ,F,hF,output_failure_probability G Q w _ _ (2*f) f 1 s hf hQ.1 F hgood⟩

/-- Corrected Algorithm3 with the actual rounded fault and vote thresholds.
No supplied accuracy event remains in the high-probability conclusion. -/
theorem exists_algorithm_three_high_probability (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (f k s : ℕ) (eps eta : ℝ) (hf : 0<f) (hk : 0<k) (heps : 0<eps) (heta : 0<eta)
    (hw : ∀ e,0≤w e) (hwpos : ∀ e∈G.edgeSet,0<w e) :
    ∃ Q : SimpleGraph V,IsMinimumFTPreserver G Q w ⌊(2+eta)*(f:ℝ)⌋₊ ∧
      ∃ F : Fin (⌊(2+eta)*(f:ℝ)⌋₊+1) → SimpleGraph V,
        (∀ i,F i≤Q ∧ (F i).IsAcyclic) ∧
        (executionLaw (V:=V) (J:=ForestComponentIndex F) f hf
          (repetitionCount (Fintype.card V) s) (input G Q w)).prob (fun a => ¬(
            IsEFTSpanner G (output G Q w ((1+eps)*(2*k-1))
              (componentEligible univ F) (componentHost F) (assignmentTape a) (⌊eta*(f:ℝ)⌋₊+1))
              w ((1+eps)*(2*k-1)) f ∧
            competitiveLightness (output G Q w ((1+eps)*(2*k-1))
              (componentEligible univ F) (componentHost F) (assignmentTape a) (⌊eta*(f:ℝ)⌋₊+1)) Q w≤
              1+64*extremalLightness (Fintype.card V) ((1+eps)*(2*k-1)+1)/eta)) ≤
          ((Fintype.card V:ℝ)^s)⁻¹ := by
  classical
  obtain ⟨Q,hQ,F,hF,hgood⟩ := exists_algorithm_three_good_event G w f k eps eta hf hk heps heta hw hwpos
  exact ⟨Q,hQ,F,hF,output_failure_probability G Q w _ _ _ f _ s hf hQ.1 F hgood⟩
end LightEFTSpanners.SampledGreedy
