import LightEFTSpanners.CorrectedVotingGuarantees

/-! The corrected paper's actual sampled output with an arbitrary valid seed.
The construction and accuracy are proved, and a genuine two-approximation
certificate transfers its weight to the optimum denominator. This module does
not assert an algorithm for computing the seed or its forest decomposition. -/

namespace LightEFTSpanners.CorrectedVoting
open SimpleGraph Finset FiniteProbability LightSpanners
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- Correctness and undivided output weight for every actual seed preserver.
The independent sample law supplies the reached-state accuracy event. -/
theorem exists_seed_high_probability {G Q : SimpleGraph V}
    (w : Sym2 V → ℝ) (q f h k s : ℕ) (eps : ℝ)
    (hQ : IsFTConnectivityPreserver G Q q) (hbudget : 2*f+h≤q+1)
    (hf : 2≤f) (hh : 0<h) (hk : 0<k) (heps : 0<eps)
    (hw : ∀ e,0≤w e) (hwpos : ∀ e∈G.edgeSet,0<w e) :
    ∃ F : Fin (q+1) → SimpleGraph V,
      (∀ i,F i≤Q ∧ (F i).IsAcyclic) ∧
      (executionLaw (V:=V) (J:=ForestComponentIndex F) f hf
        (repetitionCount (Fintype.card V) s) (input G Q w)).prob (fun a => ¬(
          IsEFTSpanner G (output G Q w ((1+eps)*(2*k-1))
            (componentEligible univ F) (componentHost F) (assignmentTape a) h)
            w ((1+eps)*(2*k-1)) f ∧
          totalWeight (output G Q w ((1+eps)*(2*k-1))
            (componentEligible univ F) (componentHost F) (assignmentTape a) h) w≤
            (1+128*(f:ℝ)*extremalLightness (Fintype.card V)
              ((1+eps)*(2*k-1)+1)/h)*totalWeight Q w)) ≤ ((Fintype.card V:ℝ)^s)⁻¹ := by
  obtain ⟨F,hF,hgood⟩ := exists_constructed_voting_weight hQ hbudget w eps k hf hh hk heps hw hwpos
  refine ⟨F,hF,?_⟩
  apply le_trans (Law.prob_mono _ (fun a hbad hacc => hbad (hgood (assignmentTape a) hacc)))
  exact constructed_inaccurate_probability G Q w _ q f h s hf hQ F

/-- A supplied two-approximate q-fault preserver yields the corrected
baseline 2 and the charged coefficient 256 against an internally attained
minimum preserver. No statistical accuracy or desired output bound is assumed. -/
theorem exists_two_approximate_seed_high_probability (G Q : SimpleGraph V)
    (w : Sym2 V → ℝ) (q f h k s : ℕ) (eps : ℝ)
    (hQ : IsFTConnectivityPreserver G Q q)
    (happrox : ∀ R,IsMinimumFTPreserver G R w q → totalWeight Q w≤2*totalWeight R w)
    (hbudget : 2*f+h≤q+1) (hf : 2≤f) (hh : 0<h) (hk : 0<k) (heps : 0<eps)
    (hw : ∀ e,0≤w e) (hwpos : ∀ e∈G.edgeSet,0<w e) :
    ∃ R : SimpleGraph V,IsMinimumFTPreserver G R w q ∧
      ∃ F : Fin (q+1) → SimpleGraph V,
        (∀ i,F i≤Q ∧ (F i).IsAcyclic) ∧
        (executionLaw (V:=V) (J:=ForestComponentIndex F) f hf
          (repetitionCount (Fintype.card V) s) (input G Q w)).prob (fun a => ¬(
            IsEFTSpanner G (output G Q w ((1+eps)*(2*k-1))
              (componentEligible univ F) (componentHost F) (assignmentTape a) h)
              w ((1+eps)*(2*k-1)) f ∧
            competitiveLightness (output G Q w ((1+eps)*(2*k-1))
              (componentEligible univ F) (componentHost F) (assignmentTape a) h) R w≤
              2+256*(f:ℝ)*extremalLightness (Fintype.card V)
                ((1+eps)*(2*k-1)+1)/h)) ≤ ((Fintype.card V:ℝ)^s)⁻¹ := by
  obtain ⟨R,hR⟩ := exists_minimum_preserver G w q
  obtain ⟨F,hF,hprob⟩ := exists_seed_high_probability w q f h k s eps hQ
    hbudget hf hh hk heps hw hwpos
  refine ⟨R,hR,F,hF,?_⟩
  apply (Law.prob_mono _ ?_).trans hprob
  intro a hbad hgood
  apply hbad
  refine ⟨hgood.1,?_⟩
  have hL := extremalLightness_nonneg (Fintype.card V) (actual_threshold_gt_two heps hk)
  have hC : 0≤1+128*(f:ℝ)*extremalLightness (Fintype.card V)
      ((1+eps)*(2*k-1)+1)/h := by positivity
  by_cases hz : totalWeight R w=0
  · simp only [competitiveLightness,hz,div_zero]
    positivity
  · have hn : 0≤totalWeight R w := by
      unfold totalWeight
      exact sum_nonneg (fun e _ => hw e)
    have hp : 0<totalWeight R w := lt_of_le_of_ne hn (Ne.symm hz)
    apply (div_le_iff₀ hp).mpr
    calc
      _ ≤ (1+128*(f:ℝ)*extremalLightness (Fintype.card V)
          ((1+eps)*(2*k-1)+1)/h)*totalWeight Q w := hgood.2
      _ ≤ (1+128*(f:ℝ)*extremalLightness (Fintype.card V)
          ((1+eps)*(2*k-1)+1)/h)*(2*totalWeight R w) :=
        mul_le_mul_of_nonneg_left (happrox R hR) hC
      _ = _ := by ring

end LightEFTSpanners.CorrectedVoting
