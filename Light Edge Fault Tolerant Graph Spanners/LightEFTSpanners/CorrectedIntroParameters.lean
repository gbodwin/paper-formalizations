import LightEFTSpanners.NativeSquareRootOutput
import LightEFTSpanners.NativePaperParameters

/-! Exact stretch parameters for the corrected introduction.  These wrappers
keep the original graph's vertex and edge identities and the attained native
connectivity optimum.  The seed and pruning costs remain explicit. -/

namespace LightEFTSpanners.NativeWeighted.CorrectedIntro
open Finset LightSpanners
open scoped NNReal
attribute [local instance] Classical.propDecidable

/-- Changing the algorithm's epsilon makes its stretch-plus-one exactly the
weighted-girth parameter printed in the corrected introduction. -/
noncomputable def epsilon (eps : ℝ≥0) (k : ℕ) : ℝ≥0 :=
  (2*k : ℕ) * eps / (2*k-1 : ℕ)

noncomputable def stretch (eps : ℝ≥0) (k : ℕ) : ℝ≥0 :=
  nativePaperStretch (epsilon eps k) k

theorem epsilon_coe (eps : ℝ≥0) {k : ℕ} (hk : 0 < k) :
    (epsilon eps k : ℝ) = 2*(k : ℝ)*(eps : ℝ)/(2*(k : ℝ)-1) := by
  simp only [epsilon, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast,
    Nat.cast_sub (show 1 ≤ 2*k by omega), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  norm_num

theorem epsilon_pos {eps : ℝ≥0} {k : ℕ} (heps : 0 < eps) (hk : 0 < k) :
    0 < epsilon eps k := by
  unfold epsilon
  exact div_pos (mul_pos (by exact_mod_cast (show 0 < 2*k by omega)) heps)
    (by exact_mod_cast (show 0 < 2*k-1 by omega))

theorem le_epsilon (eps : ℝ≥0) {k : ℕ} (hk : 0 < k) : eps ≤ epsilon eps k := by
  apply NNReal.coe_le_coe.mp
  rw [epsilon_coe eps hk]
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  apply (le_div_iff₀ (show 0 < 2*(k : ℝ)-1 by linarith)).mpr
  nlinarith [NNReal.coe_nonneg eps]

theorem epsilon_le_two_mul (eps : ℝ≥0) {k : ℕ} (hk : 0 < k) :
    epsilon eps k ≤ 2*eps := by
  apply NNReal.coe_le_coe.mp
  rw [epsilon_coe eps hk, NNReal.coe_mul, NNReal.coe_ofNat]
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  apply (div_le_iff₀ (show 0 < 2*(k : ℝ)-1 by linarith)).mpr
  nlinarith [NNReal.coe_nonneg eps]

theorem stretch_coe (eps : ℝ≥0) {k : ℕ} (hk : 0 < k) :
    (stretch eps k : ℝ) = (1+(eps : ℝ))*2*(k : ℝ)-1 := by
  rw [stretch, nativePaperStretch_coe _ hk, epsilon_coe eps hk]
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  field_simp [show 2*(k : ℝ)-1 ≠ 0 by linarith]
  ring

theorem epsilon_stretch_identity (eps : ℝ≥0) {k : ℕ} (hk : 0 < k) :
    (1+(epsilon eps k : ℝ))*(2*(k : ℝ)-1) = (1+(eps : ℝ))*2*(k : ℝ)-1 := by
  calc
    _ = (stretch eps k : ℝ) := (nativePaperStretch_coe _ hk).symm
    _ = _ := stretch_coe eps hk

/-- This is the precise factor hidden by the introduction's O(epsilon). -/
theorem stretch_le_two_epsilon (eps : ℝ≥0) {k : ℕ} (hk : 0 < k) :
    stretch eps k ≤ nativePaperStretch (2*eps) k := by
  unfold stretch nativePaperStretch
  exact mul_le_mul_of_nonneg_right (add_le_add le_rfl (epsilon_le_two_mul eps hk))
    (by positivity)

theorem stretch_gt_one {eps : ℝ≥0} {k : ℕ} (heps : 0 < eps) (hk : 0 < k) :
    1 < stretch eps k := by
  apply NNReal.coe_lt_coe.mp
  rw [NNReal.coe_one, stretch_coe eps hk]
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have heps' : (0 : ℝ) < eps := by exact_mod_cast heps
  nlinarith

theorem threshold_coe (eps : ℝ≥0) {k : ℕ} (hk : 0 < k) :
    ((stretch eps k+1 : ℝ≥0) : ℝ) = (1+(eps : ℝ))*2*(k : ℝ) := by
  rw [NNReal.coe_add, NNReal.coe_one, stretch_coe eps hk]
  ring

theorem threshold_gt_two {eps : ℝ≥0} {k : ℕ} (heps : 0 < eps) (hk : 0 < k) :
    2 < (1+(eps : ℝ))*2*(k : ℝ) := by
  rw [← threshold_coe eps hk, NNReal.coe_add, NNReal.coe_one]
  have h : (1 : ℝ) < stretch eps k := by exact_mod_cast stretch_gt_one heps hk
  linarith

variable {V E : Type*} [Fintype V] [Fintype E]

/-- Actual native output at the corrected introduction's exact lambda
argument, retaining its additive seed baseline and pruning loss. -/
theorem exists_bound (G : Graph V E) (w : E → ℝ≥0)
    (eps : ℝ≥0) (k f q h : ℕ) (heps : 0 < eps) (hk : 0 < k)
    (hf : 0 < f) (hh : 0 < h) (hcount : 2*f+h ≤ q+1) :
    ∃ S : Finset E, IsEFTSpanner G w (inputEdges G) S f (stretch eps k) ∧
      (totalWeight w S : ℝ) ≤
        (1+8*(f : ℝ)*(extremalLightness (Fintype.card V)
          ((1+(eps : ℝ))*2*(k : ℝ))+1)/(h : ℝ)) *
          (minimumPreserverWeight G w (inputEdges G) q : ℝ) := by
  simpa only [threshold_coe eps hk] using
    exists_native_minimum_output_bound G w (stretch eps k) (stretch_gt_one heps hk)
      f q h hf hh hcount

/-- The corrected square-root upper endpoint has exact lambda argument
(1+epsilon)2k and stretch (1+O(epsilon))(2k-1). -/
theorem exists_sqrt_bound (G : Graph V E) (w : E → ℝ≥0)
    (eps : ℝ≥0) (k f : ℕ) (heps : 0 < eps) (hk : 0 < k) (hf : 0 < f) :
    ∃ S : Finset E, IsEFTSpanner G w (inputEdges G) S f (stretch eps k) ∧
      (totalWeight w S : ℝ) ≤
        (1+16*Real.sqrt (f : ℝ)*(extremalLightness (Fintype.card V)
          ((1+(eps : ℝ))*2*(k : ℝ))+1)) *
          (minimumPreserverWeight G w (inputEdges G) (2*f) : ℝ) := by
  simpa only [threshold_coe eps hk] using
    exists_native_sqrt_bound G w (stretch eps k) (stretch_gt_one heps hk) f hf

/-- Real higher competition uses the actual floor budget from Algorithm 3;
the seed baseline remains one for unrestricted positive eta. -/
theorem exists_rounded_bound (G : Graph V E) (w : E → ℝ≥0)
    (eps : ℝ≥0) (eta : ℝ) (k f : ℕ) (heps : 0 < eps) (heta : 0 < eta)
    (hk : 0 < k) (hf : 0 < f) :
    ∃ S : Finset E, IsEFTSpanner G w (inputEdges G) S f (stretch eps k) ∧
      (totalWeight w S : ℝ) ≤
        (1+8*(extremalLightness (Fintype.card V)
          ((1+(eps : ℝ))*2*(k : ℝ))+1)/eta) *
          (minimumPreserverWeight G w (inputEdges G) ⌊(2+eta)*(f : ℝ)⌋₊ : ℝ) := by
  obtain ⟨S, hS, hw⟩ := exists_bound G w eps k f ⌊(2+eta)*(f : ℝ)⌋₊
    (⌊eta*(f : ℝ)⌋₊+1) heps hk hf (by omega) (native_rounded_host_coverage f heta.le).le
  refine ⟨S, hS, hw.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (NNReal.coe_nonneg _)
  exact native_rounded_coefficient f heta
    (by have h := extremalLightness_nonneg (Fintype.card V) (threshold_gt_two heps hk)
        positivity)

/-- The numerical extremal envelope is valid for every positive epsilon;
the factor epsilon-prime is at least epsilon. -/
theorem extremal_envelope (n : ℕ) {eps : ℝ≥0} {k : ℕ}
    (heps : 0 < eps) (hk : 0 < k) :
    extremalLightness n ((1+(eps : ℝ))*2*(k : ℝ))+1 ≤
      9+2048/(eps : ℝ)*(n : ℝ)^((k : ℝ)⁻¹) := by
  have h := nativePaper_extremal_envelope n (epsilon_pos heps hk) hk
  change extremalLightness n ((stretch eps k+1 : ℝ≥0) : ℝ)+1 ≤ _ at h
  rw [threshold_coe eps hk] at h
  have heps' : (0 : ℝ) < eps := by exact_mod_cast heps
  have hmono : (eps : ℝ) ≤ epsilon eps k := by exact_mod_cast le_epsilon eps hk
  have hdiv : 2048/(epsilon eps k : ℝ) ≤ 2048/(eps : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) heps' hmono
  exact h.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hdiv
    (Real.rpow_nonneg (by positivity) _)))

theorem exists_sqrt_numeric (G : Graph V E) (w : E → ℝ≥0)
    (eps : ℝ≥0) (k f : ℕ) (heps : 0 < eps) (hk : 0 < k) (hf : 0 < f) :
    ∃ S : Finset E, IsEFTSpanner G w (inputEdges G) S f (stretch eps k) ∧
      (totalWeight w S : ℝ) ≤
        (1+16*Real.sqrt (f : ℝ)*(9+2048/(eps : ℝ)*
          (Fintype.card V : ℝ)^((k : ℝ)⁻¹))) *
          (minimumPreserverWeight G w (inputEdges G) (2*f) : ℝ) := by
  obtain ⟨S, hS, hw⟩ := exists_sqrt_bound G w eps k f heps hk hf
  refine ⟨S, hS, hw.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (NNReal.coe_nonneg _)
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (extremal_envelope (Fintype.card V) heps hk) (by positivity))

theorem exists_rounded_numeric (G : Graph V E) (w : E → ℝ≥0)
    (eps : ℝ≥0) (eta : ℝ) (k f : ℕ) (heps : 0 < eps) (heta : 0 < eta)
    (hk : 0 < k) (hf : 0 < f) :
    ∃ S : Finset E, IsEFTSpanner G w (inputEdges G) S f (stretch eps k) ∧
      (totalWeight w S : ℝ) ≤
        (1+8*(9+2048/(eps : ℝ)*(Fintype.card V : ℝ)^((k : ℝ)⁻¹))/eta) *
          (minimumPreserverWeight G w (inputEdges G) ⌊(2+eta)*(f : ℝ)⌋₊ : ℝ) := by
  obtain ⟨S, hS, hw⟩ := exists_rounded_bound G w eps eta k f heps heta hk hf
  refine ⟨S, hS, hw.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (NNReal.coe_nonneg _)
  apply add_le_add le_rfl
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
    (extremal_envelope (Fintype.card V) heps hk) (by norm_num)) heta.le

/-- The explicit epsilon-inverse form uses the accepted epsilon≤1 domain. -/
theorem numerical_envelope_le {n k : ℕ} {eps : ℝ≥0}
    (hn : 1 ≤ n) (heps : 0 < eps) (heps1 : eps ≤ 1) :
    9+2048/(eps : ℝ)*(n : ℝ)^((k : ℝ)⁻¹) ≤
      2057/(eps : ℝ)*(n : ℝ)^((k : ℝ)⁻¹) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have heps' : (0 : ℝ) < eps := by exact_mod_cast heps
  have heps1' : (eps : ℝ) ≤ 1 := by exact_mod_cast heps1
  have hp : (1 : ℝ) ≤ (n : ℝ)^((k : ℝ)⁻¹) :=
    Real.one_le_rpow hn' (by positivity)
  have hi : (1 : ℝ) ≤ (eps : ℝ)⁻¹ := (one_le_inv₀ heps').mpr heps1'
  have hh : (1 : ℝ) ≤ (eps : ℝ)⁻¹*(n : ℝ)^((k : ℝ)⁻¹) :=
    one_le_mul_of_one_le_of_one_le hi hp
  simp only [div_eq_mul_inv]
  nlinarith

/-- Explicit n^(1/k)/epsilon with the seed add-back still visible. -/
theorem exists_sqrt_inverse_epsilon (G : Graph V E) (w : E → ℝ≥0)
    (eps : ℝ≥0) (k f : ℕ) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hk : 0 < k) (hf : 0 < f) (hn : 1 ≤ Fintype.card V) :
    ∃ S : Finset E, IsEFTSpanner G w (inputEdges G) S f (stretch eps k) ∧
      (totalWeight w S : ℝ) ≤
        (1+32912*Real.sqrt (f : ℝ)/(eps : ℝ)*(Fintype.card V : ℝ)^((k : ℝ)⁻¹)) *
          (minimumPreserverWeight G w (inputEdges G) (2*f) : ℝ) := by
  obtain ⟨S, hS, hw⟩ := exists_sqrt_numeric G w eps k f heps hk hf
  refine ⟨S, hS, hw.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (NNReal.coe_nonneg _)
  have hh := mul_le_mul_of_nonneg_left (numerical_envelope_le (k := k) hn heps heps1)
    (show 0 ≤ 16*Real.sqrt (f : ℝ) by positivity)
  calc
    _ ≤ 1+16*Real.sqrt (f : ℝ)*(2057/(eps : ℝ)*(Fintype.card V : ℝ)^((k : ℝ)⁻¹)) :=
      add_le_add le_rfl hh
    _ = _ := by ring

theorem exists_rounded_inverse_epsilon (G : Graph V E) (w : E → ℝ≥0)
    (eps : ℝ≥0) (eta : ℝ) (k f : ℕ) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (heta : 0 < eta) (hk : 0 < k) (hf : 0 < f) (hn : 1 ≤ Fintype.card V) :
    ∃ S : Finset E, IsEFTSpanner G w (inputEdges G) S f (stretch eps k) ∧
      (totalWeight w S : ℝ) ≤
        (1+16456/(eps : ℝ)/eta*(Fintype.card V : ℝ)^((k : ℝ)⁻¹)) *
          (minimumPreserverWeight G w (inputEdges G) ⌊(2+eta)*(f : ℝ)⌋₊ : ℝ) := by
  obtain ⟨S, hS, hw⟩ := exists_rounded_numeric G w eps eta k f heps heta hk hf
  refine ⟨S, hS, hw.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (NNReal.coe_nonneg _)
  have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
    (numerical_envelope_le (k := k) hn heps heps1) (show (0 : ℝ) ≤ 8 by norm_num)) heta.le
  calc
    _ ≤ 1+8*(2057/(eps : ℝ)*(Fintype.card V : ℝ)^((k : ℝ)⁻¹))/eta :=
      add_le_add le_rfl hh
    _ = _ := by ring

end LightEFTSpanners.NativeWeighted.CorrectedIntro
