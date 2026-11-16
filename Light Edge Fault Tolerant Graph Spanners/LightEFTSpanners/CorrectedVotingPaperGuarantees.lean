import LightEFTSpanners.CorrectedVotingApproximateSeed

/-! Algorithm 2 and the rounded Algorithm 3 with the corrected paper's
sample rate, vote threshold, concentration error, and two-approximate seed.
The hypotheses certify the seed, not the desired final spanner or its weight.
Computing that seed and its packing efficiently remains a separate question. -/

namespace LightEFTSpanners.CorrectedVoting
open SimpleGraph Finset FiniteProbability LightSpanners
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

theorem algorithm_two_two_approximate_high_probability (G Q : SimpleGraph V)
    (w : Sym2 V → ℝ) (f k s : ℕ) (eps : ℝ)
    (hQ : IsFTConnectivityPreserver G Q (2*f))
    (happrox : ∀ R,IsMinimumFTPreserver G R w (2*f) → totalWeight Q w≤2*totalWeight R w)
    (hf : 2≤f) (hk : 0<k) (heps : 0<eps)
    (hw : ∀ e,0≤w e) (hwpos : ∀ e∈G.edgeSet,0<w e) :
    ∃ R : SimpleGraph V,IsMinimumFTPreserver G R w (2*f) ∧
      ∃ F : Fin (2*f+1) → SimpleGraph V,
        (∀ i,F i≤Q ∧ (F i).IsAcyclic) ∧
        (executionLaw (V:=V) (J:=ForestComponentIndex F) f hf
          (repetitionCount (Fintype.card V) s) (input G Q w)).prob (fun a => ¬(
            IsEFTSpanner G (output G Q w ((1+eps)*(2*k-1))
              (componentEligible univ F) (componentHost F) (assignmentTape a) 1)
              w ((1+eps)*(2*k-1)) f ∧
            competitiveLightness (output G Q w ((1+eps)*(2*k-1))
              (componentEligible univ F) (componentHost F) (assignmentTape a) 1) R w≤
              2+256*(f:ℝ)*extremalLightness (Fintype.card V)
                ((1+eps)*(2*k-1)+1))) ≤ ((Fintype.card V:ℝ)^s)⁻¹ := by
  simpa only [Nat.cast_one,div_one] using
    exists_two_approximate_seed_high_probability G Q w (2*f) f 1 k s eps
      hQ happrox (by omega) hf (by decide) hk heps hw hwpos

theorem algorithm_three_two_approximate_high_probability (G Q : SimpleGraph V)
    (w : Sym2 V → ℝ) (f k s : ℕ) (eps eta : ℝ)
    (hQ : IsFTConnectivityPreserver G Q ⌊(2+eta)*(f:ℝ)⌋₊)
    (happrox : ∀ R,IsMinimumFTPreserver G R w ⌊(2+eta)*(f:ℝ)⌋₊ →
      totalWeight Q w≤2*totalWeight R w)
    (hf : 2≤f) (hk : 0<k) (heps : 0<eps) (heta : 0<eta)
    (hw : ∀ e,0≤w e) (hwpos : ∀ e∈G.edgeSet,0<w e) :
    ∃ R : SimpleGraph V,IsMinimumFTPreserver G R w ⌊(2+eta)*(f:ℝ)⌋₊ ∧
      ∃ F : Fin (⌊(2+eta)*(f:ℝ)⌋₊+1) → SimpleGraph V,
        (∀ i,F i≤Q ∧ (F i).IsAcyclic) ∧
        (executionLaw (V:=V) (J:=ForestComponentIndex F) f hf
          (repetitionCount (Fintype.card V) s) (input G Q w)).prob (fun a => ¬(
            IsEFTSpanner G (output G Q w ((1+eps)*(2*k-1))
              (componentEligible univ F) (componentHost F) (assignmentTape a)
                (⌊eta*(f:ℝ)⌋₊+1)) w ((1+eps)*(2*k-1)) f ∧
            competitiveLightness (output G Q w ((1+eps)*(2*k-1))
              (componentEligible univ F) (componentHost F) (assignmentTape a)
                (⌊eta*(f:ℝ)⌋₊+1)) R w≤
              2+256*extremalLightness (Fintype.card V)
                ((1+eps)*(2*k-1)+1)/eta)) ≤ ((Fintype.card V:ℝ)^s)⁻¹ := by
  have hbudget : 2*f+(⌊eta*(f:ℝ)⌋₊+1)≤⌊(2+eta)*(f:ℝ)⌋₊+1 := by
    rw [rounded_fault_budget f heta.le]
    omega
  obtain ⟨R,hR,F,hF,hprob⟩ := exists_two_approximate_seed_high_probability G Q w
    ⌊(2+eta)*(f:ℝ)⌋₊ f (⌊eta*(f:ℝ)⌋₊+1) k s eps hQ happrox
    hbudget hf (Nat.succ_pos _) hk heps hw hwpos
  refine ⟨R,hR,F,hF,?_⟩
  apply (Law.prob_mono _ ?_).trans hprob
  intro a hbad hgood
  apply hbad
  refine ⟨hgood.1,hgood.2.trans ?_⟩
  have hL := extremalLightness_nonneg (Fintype.card V) (actual_threshold_gt_two heps hk)
  have hc := rounded_charging_le f heta (mul_nonneg (show (0:ℝ)≤32 by norm_num) hL)
  have hb : 1+256*(f:ℝ)*extremalLightness (Fintype.card V)
      ((1+eps)*(2*k-1)+1)/(⌊eta*(f:ℝ)⌋₊+1:ℕ) ≤
      1+256*extremalLightness (Fintype.card V) ((1+eps)*(2*k-1)+1)/eta := by
    convert hc using 1 <;> ring
  linarith

end LightEFTSpanners.CorrectedVoting
