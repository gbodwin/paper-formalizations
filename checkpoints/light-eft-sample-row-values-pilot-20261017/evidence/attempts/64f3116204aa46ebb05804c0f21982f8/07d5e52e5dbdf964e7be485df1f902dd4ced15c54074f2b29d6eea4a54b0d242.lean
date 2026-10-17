import LightEFTSpanners.NativeMinimumOutput
import LightEFTSpanners.ExactExtremalDefinition
import Mathlib.Algebra.Order.Floor.Semiring

/-! Corrected paper stretch and numerical bounds for the original-ID native
construction. The bound at competition 2f remains linear in f. -/
namespace LightEFTSpanners.NativeWeighted
open Finset LightSpanners
open scoped NNReal
variable {V E : Type*} [Fintype V] [Fintype E]
attribute [local instance] Classical.propDecidable

noncomputable def nativePaperStretch (eps : ℝ≥0) (k : ℕ) : ℝ≥0 :=
  (1+eps) * (2*k-1 : ℕ)

theorem nativePaperStretch_coe (eps : ℝ≥0) {k : ℕ} (hk : 0 < k) :
    (nativePaperStretch eps k : ℝ) = (1+(eps : ℝ))*(2*(k : ℝ)-1) := by
  rw [nativePaperStretch,NNReal.coe_mul,NNReal.coe_add,NNReal.coe_one,NNReal.coe_natCast,
    Nat.cast_sub (show 1 ≤ 2*k by omega),Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]

theorem nativePaperStretch_gt_one {eps : ℝ≥0} {k : ℕ} (heps : 0 < eps) (hk : 0 < k) :
    1 < nativePaperStretch eps k := by
  have hn : (1 : ℝ≥0) ≤ (2*k-1 : ℕ) := by exact_mod_cast (show 1 ≤ 2*k-1 by omega)
  unfold nativePaperStretch
  nlinarith

/-- The existing numerical extremal theorem at the actual stretch+1 threshold.
Adding the pruning loss changes its baseline from 8 to 9. -/
theorem nativePaper_extremal_envelope (n : ℕ) {eps : ℝ≥0} {k : ℕ}
    (heps : 0 < eps) (hk : 0 < k) :
    extremalLightness n ((nativePaperStretch eps k+1 : ℝ≥0) : ℝ)+1 ≤
      9+2048/(eps : ℝ)*(n : ℝ)^((k : ℝ)⁻¹) := by
  have h := extremalLightness_corrected_coarse_bound n (eps := (eps : ℝ)) (by exact_mod_cast heps) hk
  rw [NNReal.coe_add,NNReal.coe_one,nativePaperStretch_coe eps hk]
  linarith

/-- Complete native multigraph existence with an attained q-optimum and
explicit integer host coverage. This does not improve f/h to sqrt(f). -/
theorem exists_native_paper_bound (G : Graph V E) (w : E → ℝ≥0)
    (eps : ℝ≥0) (k f q h : ℕ) (heps : 0 < eps) (hk : 0 < k)
    (hf : 0 < f) (hh : 0 < h) (hcount : 2*f+h ≤ q+1) :
    ∃ S : Finset E, IsEFTSpanner G w (inputEdges G) S f (nativePaperStretch eps k) ∧
      (totalWeight w S : ℝ) ≤
        (1+8*(f : ℝ)*(9+2048/(eps : ℝ)*(Fintype.card V : ℝ)^((k : ℝ)⁻¹))/(h : ℝ)) *
          (minimumPreserverWeight G w (inputEdges G) q : ℝ) := by
  obtain ⟨S,hS,hw⟩ := exists_native_minimum_output_bound G w (nativePaperStretch eps k)
    (nativePaperStretch_gt_one heps hk) f q h hf hh hcount
  refine ⟨S,hS,hw.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (NNReal.coe_nonneg _)
  apply add_le_add le_rfl
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left (nativePaper_extremal_envelope (Fintype.card V) heps hk) (by positivity)

/-- q=2f, h=1: a linear-f bound, not Theorem 11's square-root improvement. -/
theorem exists_native_paper_baseline (G : Graph V E) (w : E → ℝ≥0)
    (eps : ℝ≥0) (k f : ℕ) (heps : 0 < eps) (hk : 0 < k) (hf : 0 < f) :
    ∃ S : Finset E, IsEFTSpanner G w (inputEdges G) S f (nativePaperStretch eps k) ∧
      (totalWeight w S : ℝ) ≤
        (1+8*(f : ℝ)*(9+2048/(eps : ℝ)*(Fintype.card V : ℝ)^((k : ℝ)⁻¹))) *
          (minimumPreserverWeight G w (inputEdges G) (2*f) : ℝ) := by
  simpa using exists_native_paper_bound G w eps k f (2*f) 1 heps hk hf (by omega) (by omega)

/-- The integer interpretation of real competition gives exactly h positive
votes, with no ceil or extra vote hidden at nonintegral eta*f. -/
theorem native_rounded_budget (f : ℕ) {eta : ℝ} (heta : 0 ≤ eta) :
    ⌊(2+eta)*(f : ℝ)⌋₊ = 2*f+⌊eta*(f : ℝ)⌋₊ := by
  rw [show (2+eta)*(f : ℝ) = eta*f+(2*f : ℕ) by push_cast; ring]
  rw [Nat.floor_add_natCast (by positivity)]
  omega

theorem native_rounded_host_coverage (f : ℕ) {eta : ℝ} (heta : 0 ≤ eta) :
    2*f+(⌊eta*(f : ℝ)⌋₊+1) = ⌊(2+eta)*(f : ℝ)⌋₊+1 := by
  rw [native_rounded_budget f heta]
  omega

/-- B is an explicit nonnegative envelope, including the pruning loss. -/
theorem native_rounded_coefficient (f : ℕ) {eta B : ℝ} (heta : 0 < eta) (hB : 0 ≤ B) :
    1+8*(f : ℝ)*B/(⌊eta*(f : ℝ)⌋₊+1 : ℕ) ≤ 1+8*B/eta := by
  have hd : (0 : ℝ) < (⌊eta*(f : ℝ)⌋₊+1 : ℕ) := by positivity
  have hb := Nat.lt_floor_add_one (eta*(f : ℝ))
  have hp := mul_le_mul_of_nonneg_left hb.le (show 0 ≤ 8*B by positivity)
  have hdiv : 8*(f : ℝ)*B/(⌊eta*(f : ℝ)⌋₊+1 : ℕ) ≤ 8*B/eta := by
    apply (div_le_div_iff₀ hd heta).mpr
    push_cast
    nlinarith
  linarith

/-- Rounded higher competition for the native model, with seed baseline one
and the numerical pruning envelope retained for unrestricted eta>0. -/
theorem exists_native_paper_rounded (G : Graph V E) (w : E → ℝ≥0)
    (eps : ℝ≥0) (eta : ℝ) (k f : ℕ) (heps : 0 < eps) (heta : 0 < eta)
    (hk : 0 < k) (hf : 0 < f) :
    ∃ S : Finset E, IsEFTSpanner G w (inputEdges G) S f (nativePaperStretch eps k) ∧
      (totalWeight w S : ℝ) ≤
        (1+8*(9+2048/(eps : ℝ)*(Fintype.card V : ℝ)^((k : ℝ)⁻¹))/eta) *
          (minimumPreserverWeight G w (inputEdges G) ⌊(2+eta)*(f : ℝ)⌋₊ : ℝ) := by
  obtain ⟨S,hS,hw⟩ := exists_native_paper_bound G w eps k f ⌊(2+eta)*(f : ℝ)⌋₊
    (⌊eta*(f : ℝ)⌋₊+1) heps hk hf (by omega) (native_rounded_host_coverage f heta.le).le
  refine ⟨S,hS,hw.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (native_rounded_coefficient f heta (by positivity)) (NNReal.coe_nonneg _)

end LightEFTSpanners.NativeWeighted
