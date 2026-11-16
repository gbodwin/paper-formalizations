import LightEFTSpanners.CorrectedIntroParameters
import LightEFTSpanners.CorrectedVotingPaperGuarantees

/-! The corrected introduction's exact weighted-girth parameter for the actual
1/f sampler.  The algorithm, law, rounded votes, and original fault semantics
are unchanged by this epsilon substitution.  Two-approximate seed wrappers
retain baseline two; computing a seed and forest packing efficiently is an
external requirement of the executable implementation. -/

namespace LightEFTSpanners.CorrectedIntroVoting
open SimpleGraph Finset FiniteProbability LightSpanners CorrectedVoting
open NativeWeighted.CorrectedIntro
open scoped NNReal
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

theorem exists_algorithm_two_high_probability (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (f k s : ℕ) (eps : ℝ≥0) (hf : 2≤f) (hk : 0<k) (heps : 0<eps)
    (hw : ∀ e,0≤w e) (hwpos : ∀ e∈G.edgeSet,0<w e) :
    ∃ Q : SimpleGraph V,IsMinimumFTPreserver G Q w (2*f) ∧
      ∃ F : Fin (2*f+1) → SimpleGraph V,
        (∀ i,F i≤Q ∧ (F i).IsAcyclic) ∧
        (CorrectedVoting.executionLaw (V:=V) (J:=ForestComponentIndex F) f hf
          (CorrectedVoting.repetitionCount (Fintype.card V) s) (input G Q w)).prob (fun a => ¬(
            IsEFTSpanner G (CorrectedVoting.output G Q w ((1+(eps : ℝ))*2*(k : ℝ)-1)
              (CorrectedVoting.componentEligible univ F) (CorrectedVoting.componentHost F) (CorrectedVoting.assignmentTape a) 1) w ((1+(eps : ℝ))*2*(k : ℝ)-1) f ∧
            competitiveLightness (CorrectedVoting.output G Q w ((1+(eps : ℝ))*2*(k : ℝ)-1)
              (CorrectedVoting.componentEligible univ F) (CorrectedVoting.componentHost F) (CorrectedVoting.assignmentTape a) 1) Q w≤
              1+128*(f:ℝ)*extremalLightness (Fintype.card V) ((1+(eps : ℝ))*2*(k : ℝ)))) ≤
          ((Fintype.card V:ℝ)^s)⁻¹ := by
  have heps' : (0 : ℝ) < epsilon eps k := by exact_mod_cast epsilon_pos heps hk
  simpa only [epsilon_stretch_identity eps hk, sub_add_cancel] using
    CorrectedVoting.exists_algorithm_two_high_probability G w f k s (epsilon eps k : ℝ) hf hk heps' hw hwpos

theorem exists_algorithm_three_high_probability (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (f k s : ℕ) (eps : ℝ≥0) (eta : ℝ) (hf : 2≤f) (hk : 0<k) (heps : 0<eps) (heta : 0<eta)
    (hw : ∀ e,0≤w e) (hwpos : ∀ e∈G.edgeSet,0<w e) :
    ∃ Q : SimpleGraph V,IsMinimumFTPreserver G Q w ⌊(2+eta)*(f:ℝ)⌋₊ ∧
      ∃ F : Fin (⌊(2+eta)*(f:ℝ)⌋₊+1) → SimpleGraph V,
        (∀ i,F i≤Q ∧ (F i).IsAcyclic) ∧
        (CorrectedVoting.executionLaw (V:=V) (J:=ForestComponentIndex F) f hf
          (CorrectedVoting.repetitionCount (Fintype.card V) s) (input G Q w)).prob (fun a => ¬(
            IsEFTSpanner G (CorrectedVoting.output G Q w ((1+(eps : ℝ))*2*(k : ℝ)-1)
              (CorrectedVoting.componentEligible univ F) (CorrectedVoting.componentHost F) (CorrectedVoting.assignmentTape a) (⌊eta*(f:ℝ)⌋₊+1))
              w ((1+(eps : ℝ))*2*(k : ℝ)-1) f ∧
            competitiveLightness (CorrectedVoting.output G Q w ((1+(eps : ℝ))*2*(k : ℝ)-1)
              (CorrectedVoting.componentEligible univ F) (CorrectedVoting.componentHost F) (CorrectedVoting.assignmentTape a) (⌊eta*(f:ℝ)⌋₊+1)) Q w≤
              1+128*extremalLightness (Fintype.card V) ((1+(eps : ℝ))*2*(k : ℝ))/eta)) ≤
          ((Fintype.card V:ℝ)^s)⁻¹ := by
  have heps' : (0 : ℝ) < epsilon eps k := by exact_mod_cast epsilon_pos heps hk
  simpa only [epsilon_stretch_identity eps hk, sub_add_cancel] using
    CorrectedVoting.exists_algorithm_three_high_probability G w f k s (epsilon eps k : ℝ) eta hf hk heps' heta hw hwpos

theorem algorithm_two_two_approximate_high_probability (G Q : SimpleGraph V)
    (w : Sym2 V → ℝ) (f k s : ℕ) (eps : ℝ≥0)
    (hQ : IsFTConnectivityPreserver G Q (2*f))
    (happrox : ∀ R,IsMinimumFTPreserver G R w (2*f) → totalWeight Q w≤2*totalWeight R w)
    (hf : 2≤f) (hk : 0<k) (heps : 0<eps)
    (hw : ∀ e,0≤w e) (hwpos : ∀ e∈G.edgeSet,0<w e) :
    ∃ R : SimpleGraph V,IsMinimumFTPreserver G R w (2*f) ∧
      ∃ F : Fin (2*f+1) → SimpleGraph V,
        (∀ i,F i≤Q ∧ (F i).IsAcyclic) ∧
        (CorrectedVoting.executionLaw (V:=V) (J:=ForestComponentIndex F) f hf
          (CorrectedVoting.repetitionCount (Fintype.card V) s) (input G Q w)).prob (fun a => ¬(
            IsEFTSpanner G (CorrectedVoting.output G Q w ((1+(eps : ℝ))*2*(k : ℝ)-1)
              (CorrectedVoting.componentEligible univ F) (CorrectedVoting.componentHost F) (CorrectedVoting.assignmentTape a) 1)
              w ((1+(eps : ℝ))*2*(k : ℝ)-1) f ∧
            competitiveLightness (CorrectedVoting.output G Q w ((1+(eps : ℝ))*2*(k : ℝ)-1)
              (CorrectedVoting.componentEligible univ F) (CorrectedVoting.componentHost F) (CorrectedVoting.assignmentTape a) 1) R w≤
              2+256*(f:ℝ)*extremalLightness (Fintype.card V)
                ((1+(eps : ℝ))*2*(k : ℝ)))) ≤ ((Fintype.card V:ℝ)^s)⁻¹ := by
  have heps' : (0 : ℝ) < epsilon eps k := by exact_mod_cast epsilon_pos heps hk
  simpa only [epsilon_stretch_identity eps hk, sub_add_cancel] using
    CorrectedVoting.algorithm_two_two_approximate_high_probability G Q w f k s (epsilon eps k : ℝ) hQ happrox hf hk heps' hw hwpos

theorem algorithm_three_two_approximate_high_probability (G Q : SimpleGraph V)
    (w : Sym2 V → ℝ) (f k s : ℕ) (eps : ℝ≥0) (eta : ℝ)
    (hQ : IsFTConnectivityPreserver G Q ⌊(2+eta)*(f:ℝ)⌋₊)
    (happrox : ∀ R,IsMinimumFTPreserver G R w ⌊(2+eta)*(f:ℝ)⌋₊ →
      totalWeight Q w≤2*totalWeight R w)
    (hf : 2≤f) (hk : 0<k) (heps : 0<eps) (heta : 0<eta)
    (hw : ∀ e,0≤w e) (hwpos : ∀ e∈G.edgeSet,0<w e) :
    ∃ R : SimpleGraph V,IsMinimumFTPreserver G R w ⌊(2+eta)*(f:ℝ)⌋₊ ∧
      ∃ F : Fin (⌊(2+eta)*(f:ℝ)⌋₊+1) → SimpleGraph V,
        (∀ i,F i≤Q ∧ (F i).IsAcyclic) ∧
        (CorrectedVoting.executionLaw (V:=V) (J:=ForestComponentIndex F) f hf
          (CorrectedVoting.repetitionCount (Fintype.card V) s) (input G Q w)).prob (fun a => ¬(
            IsEFTSpanner G (CorrectedVoting.output G Q w ((1+(eps : ℝ))*2*(k : ℝ)-1)
              (CorrectedVoting.componentEligible univ F) (CorrectedVoting.componentHost F) (CorrectedVoting.assignmentTape a)
                (⌊eta*(f:ℝ)⌋₊+1)) w ((1+(eps : ℝ))*2*(k : ℝ)-1) f ∧
            competitiveLightness (CorrectedVoting.output G Q w ((1+(eps : ℝ))*2*(k : ℝ)-1)
              (CorrectedVoting.componentEligible univ F) (CorrectedVoting.componentHost F) (CorrectedVoting.assignmentTape a)
                (⌊eta*(f:ℝ)⌋₊+1)) R w≤
              2+256*extremalLightness (Fintype.card V)
                ((1+(eps : ℝ))*2*(k : ℝ))/eta)) ≤ ((Fintype.card V:ℝ)^s)⁻¹ := by
  have heps' : (0 : ℝ) < epsilon eps k := by exact_mod_cast epsilon_pos heps hk
  simpa only [epsilon_stretch_identity eps hk, sub_add_cancel] using
    CorrectedVoting.algorithm_three_two_approximate_high_probability G Q w f k s (epsilon eps k : ℝ) eta hQ happrox hf hk heps' heta hw hwpos

theorem algorithm_two_two_approximate_high_probability_numeric (G Q : SimpleGraph V)
    (w : Sym2 V → ℝ) (f k s : ℕ) (eps : ℝ≥0)
    (hQ : IsFTConnectivityPreserver G Q (2*f))
    (happrox : ∀ R,IsMinimumFTPreserver G R w (2*f) → totalWeight Q w≤2*totalWeight R w)
    (hf : 2≤f) (hk : 0<k) (heps : 0<eps)
    (hw : ∀ e,0≤w e) (hwpos : ∀ e∈G.edgeSet,0<w e) :
    ∃ R : SimpleGraph V,IsMinimumFTPreserver G R w (2*f) ∧
      ∃ F : Fin (2*f+1) → SimpleGraph V,
        (∀ i,F i≤Q ∧ (F i).IsAcyclic) ∧
        (CorrectedVoting.executionLaw (V:=V) (J:=ForestComponentIndex F) f hf
          (CorrectedVoting.repetitionCount (Fintype.card V) s) (input G Q w)).prob (fun a => ¬(
            IsEFTSpanner G (CorrectedVoting.output G Q w ((1+(eps : ℝ))*2*(k : ℝ)-1)
              (CorrectedVoting.componentEligible univ F) (CorrectedVoting.componentHost F) (CorrectedVoting.assignmentTape a) 1)
              w ((1+(eps : ℝ))*2*(k : ℝ)-1) f ∧
            competitiveLightness (CorrectedVoting.output G Q w ((1+(eps : ℝ))*2*(k : ℝ)-1)
              (CorrectedVoting.componentEligible univ F) (CorrectedVoting.componentHost F) (CorrectedVoting.assignmentTape a) 1) R w≤
              2+256*(f:ℝ)*(9+2048/(eps : ℝ)*(Fintype.card V : ℝ)^((k : ℝ)⁻¹)))) ≤ ((Fintype.card V:ℝ)^s)⁻¹ := by
  obtain ⟨R, hR, F, hF, hp⟩ := algorithm_two_two_approximate_high_probability G Q w f k s eps hQ happrox hf hk heps hw hwpos
  refine ⟨R, hR, F, hF, ?_⟩
  have hL : extremalLightness (Fintype.card V) ((1+(eps : ℝ))*2*(k : ℝ)) ≤
      9+2048/(eps : ℝ)*(Fintype.card V : ℝ)^((k : ℝ)⁻¹) := by
    linarith [extremal_envelope (Fintype.card V) heps hk]
  have hc : 2+256*(f : ℝ)*extremalLightness (Fintype.card V) ((1+(eps : ℝ))*2*(k : ℝ)) ≤
      2+256*(f : ℝ)*(9+2048/(eps : ℝ)*(Fintype.card V : ℝ)^((k : ℝ)⁻¹)) :=
    add_le_add le_rfl (mul_le_mul_of_nonneg_left hL (by positivity))
  apply (Law.prob_mono _ ?_).trans hp
  intro a hbad hgood
  exact hbad ⟨hgood.1, hgood.2.trans hc⟩

theorem algorithm_three_two_approximate_high_probability_numeric (G Q : SimpleGraph V)
    (w : Sym2 V → ℝ) (f k s : ℕ) (eps : ℝ≥0) (eta : ℝ)
    (hQ : IsFTConnectivityPreserver G Q ⌊(2+eta)*(f:ℝ)⌋₊)
    (happrox : ∀ R,IsMinimumFTPreserver G R w ⌊(2+eta)*(f:ℝ)⌋₊ →
      totalWeight Q w≤2*totalWeight R w)
    (hf : 2≤f) (hk : 0<k) (heps : 0<eps) (heta : 0<eta)
    (hw : ∀ e,0≤w e) (hwpos : ∀ e∈G.edgeSet,0<w e) :
    ∃ R : SimpleGraph V,IsMinimumFTPreserver G R w ⌊(2+eta)*(f:ℝ)⌋₊ ∧
      ∃ F : Fin (⌊(2+eta)*(f:ℝ)⌋₊+1) → SimpleGraph V,
        (∀ i,F i≤Q ∧ (F i).IsAcyclic) ∧
        (CorrectedVoting.executionLaw (V:=V) (J:=ForestComponentIndex F) f hf
          (CorrectedVoting.repetitionCount (Fintype.card V) s) (input G Q w)).prob (fun a => ¬(
            IsEFTSpanner G (CorrectedVoting.output G Q w ((1+(eps : ℝ))*2*(k : ℝ)-1)
              (CorrectedVoting.componentEligible univ F) (CorrectedVoting.componentHost F) (CorrectedVoting.assignmentTape a)
                (⌊eta*(f:ℝ)⌋₊+1)) w ((1+(eps : ℝ))*2*(k : ℝ)-1) f ∧
            competitiveLightness (CorrectedVoting.output G Q w ((1+(eps : ℝ))*2*(k : ℝ)-1)
              (CorrectedVoting.componentEligible univ F) (CorrectedVoting.componentHost F) (CorrectedVoting.assignmentTape a)
                (⌊eta*(f:ℝ)⌋₊+1)) R w≤
              2+256*(9+2048/(eps : ℝ)*(Fintype.card V : ℝ)^((k : ℝ)⁻¹))/eta)) ≤ ((Fintype.card V:ℝ)^s)⁻¹ := by
  obtain ⟨R, hR, F, hF, hp⟩ := algorithm_three_two_approximate_high_probability G Q w f k s eps eta hQ happrox hf hk heps heta hw hwpos
  refine ⟨R, hR, F, hF, ?_⟩
  have hL : extremalLightness (Fintype.card V) ((1+(eps : ℝ))*2*(k : ℝ)) ≤
      9+2048/(eps : ℝ)*(Fintype.card V : ℝ)^((k : ℝ)⁻¹) := by
    linarith [extremal_envelope (Fintype.card V) heps hk]
  have hc : 2+256*extremalLightness (Fintype.card V) ((1+(eps : ℝ))*2*(k : ℝ))/eta ≤
      2+256*(9+2048/(eps : ℝ)*(Fintype.card V : ℝ)^((k : ℝ)⁻¹))/eta :=
    add_le_add le_rfl (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hL (show (0 : ℝ) ≤ 256 by norm_num)) heta.le)
  apply (Law.prob_mono _ ?_).trans hp
  intro a hbad hgood
  exact hbad ⟨hgood.1, hgood.2.trans hc⟩

end LightEFTSpanners.CorrectedIntroVoting
