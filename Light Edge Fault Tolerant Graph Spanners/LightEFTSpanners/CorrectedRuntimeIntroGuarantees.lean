import LightEFTSpanners.CorrectedRuntimeApproximateSeed

/-! The corrected introduction uses stretch (1+O(eps))(2k-1) and extremal
argument (1+eps)2k. This is an exact rational reparameterization of the actual
corrected sampled program; no monotonicity in the girth argument is assumed. -/
namespace LightEFTSpanners.CorrectedRuntime
open SimpleGraph Finset FiniteProbability LightSpanners
variable {n : ℕ}
attribute [local instance] Classical.propDecidable

def introEpsilon (eps : ℚ) (k : ℕ) : ℚ := 2*k*eps/(2*k-1)
def introStretch (eps : ℚ) (k : ℕ) : ℚ := (1+eps)*(2*k)-1

theorem introEpsilon_pos {eps : ℚ} (heps : 0<eps) {k : ℕ} (hk : 0<k) :
    0 < introEpsilon eps k := by
  have hkQ : (1:ℚ)≤k := by exact_mod_cast hk
  unfold introEpsilon
  apply div_pos
  · positivity
  · linarith

theorem introEpsilon_le_twice {eps : ℚ} (heps : 0≤eps) {k : ℕ} (hk : 0<k) :
    introEpsilon eps k≤2*eps := by
  have hkQ : (1:ℚ)≤k := by exact_mod_cast hk
  unfold introEpsilon
  apply (div_le_iff₀ (by linarith : (0:ℚ)<2*k-1)).mpr
  nlinarith [mul_nonneg heps (sub_nonneg.mpr hkQ)]

theorem paperStretch_introEpsilon (eps : ℚ) {k : ℕ} (hk : 0<k) :
    paperStretch (introEpsilon eps k) k=introStretch eps k := by
  have hkQ : (1:ℚ)≤k := by exact_mod_cast hk
  have hden : (2*(k:ℚ)-1)≠0 := by linarith
  unfold paperStretch introEpsilon introStretch
  field_simp [hden]
  ring

theorem introStretch_le_twice {eps : ℚ} (heps : 0≤eps) {k : ℕ} (hk : 0<k) :
    introStretch eps k ≤ (1+2*eps)*(2*k-1) := by
  have hkQ : (1:ℚ)≤k := by exact_mod_cast hk
  rw [← paperStretch_introEpsilon eps hk]
  unfold paperStretch
  have he : 1+introEpsilon eps k ≤ 1+2*eps := by
    linarith [introEpsilon_le_twice heps hk]
  exact mul_le_mul_of_nonneg_right he (by linarith)

@[simp] theorem introStretch_threshold (eps : ℚ) (k : ℕ) :
    (introStretch eps k:ℝ)+1=(1+(eps:ℝ))*(2*k) := by
  simp [introStretch]

theorem exists_two_approximate_seed_intro_high_probability (G Q : SimpleGraph (Fin n))
    (w : Sym2 (Fin n) → ℚ) (q f h k s : ℕ) (eps : ℚ)
    (hQ : IsFTConnectivityPreserver G Q q)
    (happrox : ∀ R,IsMinimumFTPreserver G R (fun e => (w e:ℝ)) q → totalWeight Q (fun e => (w e:ℝ))≤2*totalWeight R (fun e => (w e:ℝ)))
    (hbudget : 2*f+h≤q+1) (hf : 2≤f) (hh : 0<h) (hk : 0<k) (heps : 0<eps)
    (hw : ∀ e,0≤w e) (hwpos : ∀ e∈G.edgeSet,0<w e) :
    ∃ R : SimpleGraph (Fin n),IsMinimumFTPreserver G R (fun e => (w e:ℝ)) q ∧
      ∃ F : Fin (q+1) → SimpleGraph (Fin n),
        (∀ i,F i≤Q ∧ (F i).IsAcyclic) ∧
        (CorrectedVoting.executionLaw (V:=Fin n) (J:=ForestComponentIndex F) f hf
          (CorrectedVoting.repetitionCount (Fintype.card (Fin n)) s) (input G Q (fun e => (w e:ℝ)))).prob (fun a => ¬(
            IsEFTSpanner G (output G Q w hw (introStretch eps k)
              (CorrectedVoting.componentEligible univ F) (CorrectedVoting.componentHost F) (CorrectedVoting.assignmentTape a) h)
              (fun e => (w e:ℝ)) (introStretch eps k:ℝ) f ∧
            competitiveLightness (output G Q w hw (introStretch eps k)
              (CorrectedVoting.componentEligible univ F) (CorrectedVoting.componentHost F) (CorrectedVoting.assignmentTape a) h) R (fun e => (w e:ℝ))≤
              2+256*(f:ℝ)*extremalLightness n
                ((1+(eps:ℝ))*(2*k))/h)) ≤ ((n:ℝ)^s)⁻¹ := by
  obtain ⟨R,hR,F,hF,hprob⟩ := exists_two_approximate_seed_high_probability G Q w
    q f h k s (introEpsilon eps k) hQ happrox hbudget hf hh hk
      (introEpsilon_pos heps hk) hw hwpos
  refine ⟨R,hR,F,hF,?_⟩
  simpa only [paperStretch_introEpsilon eps hk,introStretch_threshold] using hprob

end LightEFTSpanners.CorrectedRuntime
