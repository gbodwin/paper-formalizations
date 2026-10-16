import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-! Quantitative concentration for actual independent finite samples. -/
namespace LightEFTSpanners.FiniteProbability
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- The two-sided Hoeffding estimate at the literal accuracy used by voting. -/
theorem bounded_mean_tail (m : ℕ) (hm : 0<m) (X : Fin m → Ω → ℝ)
    (hX : ∀ i, AEMeasurable (X i) μ) (hind : iIndepFun X μ)
    (hb : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (0:ℝ) 1) :
    μ.real {ω | 1/8 < |(∑ i, (X i ω - ∫ x, X i x ∂μ))/(m:ℝ)|} ≤
      2 * Real.exp (-(m:ℝ)/32) := by
  have hmR : (0:ℝ)<m := by exact_mod_cast hm
  let Y : Fin m → Ω → ℝ := fun i ω => X i ω - ∫ x, X i x ∂μ
  have hY : iIndepFun Y μ := hind.comp (fun i x => x - ∫ y, X i y ∂μ)
    (fun _ => measurable_id.sub_const _)
  have hsub : ∀ i, HasSubgaussianMGF (Y i) (1/4) μ := by
    intro i
    convert hasSubgaussianMGF_of_mem_Icc (hX i) (hb i) using 1
    norm_num [Y]
  have hp := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hY
    (s := univ) (fun i _ => hsub i) (ε := (m:ℝ)/8) (by positivity)
  have hn := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
    (hY.comp (fun _ x => -x) (fun _ => measurable_neg))
    (s := univ) (c := fun _ => (1/4:ℝ≥0))
    (fun i _ => (hsub i).neg) (ε := (m:ℝ)/8) (by positivity)
  have he : -((m:ℝ)/8)^2 / (2 * ((m:ℝ)/4)) = -(m:ℝ)/32 := by
    field_simp
    ring
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    NNReal.coe_natCast, NNReal.coe_div,
    NNReal.coe_ofNat, mul_one_div, Function.comp_apply] at hp hn
  rw [he] at hp hn
  calc
    _ ≤ μ.real ({ω | (m:ℝ)/8 ≤ ∑ i, Y i ω} ∪
        {ω | (m:ℝ)/8 ≤ ∑ i, -Y i ω}) := by
      refine measureReal_mono ?_ (by finiteness)
      intro ω hω
      change 1/8 < |(∑ i, Y i ω)/(m:ℝ)| at hω
      have h := (lt_abs.mp hω)
      simp only [Set.mem_union, Set.mem_ofPred_eq, sum_neg_distrib]
      rcases h with h | h
      · left
        have hh := (lt_div_iff₀ hmR).mp h
        linarith
      · right
        rw [← neg_div] at h
        have hh := (lt_div_iff₀ hmR).mp h
        linarith
    _ ≤ _ := (measureReal_union_le _ _).trans (by linarith)
end LightEFTSpanners.FiniteProbability
