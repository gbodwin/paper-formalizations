import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-! Exact checks of two arXiv v1 formulas used in Appendix A. -/

namespace OnlineReachabilityPreservers.SourceAudit

open Finset

/-- A finite counterexample to the printed Lemma 25 denominator.
The four entries are 1, 1, 2, 2, with m = 2, a = 3/2 and t = 0. -/
theorem lemma25_printed_counterexample :
    ∃ (x : Fin 4 → ℚ) (m a t : ℚ),
      (∀ i, x i ≤ m) ∧ (∑ i, x i) / 4 ≥ a ∧ t < a ∧ a < m ∧
      ((univ.filter (fun i => t ≤ x i)).card : ℚ) < (a - t) / (m - a) * 4 := by
  refine ⟨fun i => if i.val < 2 then 1 else 2, 2, 3/2, 0, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · norm_num [Fin.sum_univ_four]
  · norm_num
  · norm_num
  · have h : (univ.filter (fun i : Fin 4 => (0 : ℚ) ≤ (if i.val < 2 then 1 else 2))) =
        univ := by decide
    rw [h]
    norm_num

/-- The corrected tail count, in the division-free form needed for Lemma 26. -/
theorem lemma25_tail_count {I : Type*} (s : Finset I) (x : I → ℝ) (m a t : ℝ)
    (bound : ∀ i ∈ s, x i ≤ m) (avg : a * s.card ≤ ∑ i ∈ s, x i) :
    (a - t) * s.card ≤ (m - t) * (s.filter (fun i => t ≤ x i)).card := by
  classical
  let f := s.filter (fun i => t ≤ x i)
  have hsub : f ⊆ s := filter_subset _ _
  have hcount : ((s \ f).card : ℝ) + f.card = s.card := by
    exact_mod_cast card_sdiff_add_card_eq_card hsub
  have hd : Disjoint (s \ f) f :=
    disjoint_left.mpr (fun _ hi hf => (mem_sdiff.mp hi).2 hf)
  have h1 : (∑ i ∈ f, x i) ≤ f.card * m := by
    calc
      _ ≤ ∑ _i ∈ f, m := sum_le_sum (fun i hi => bound i (hsub hi))
      _ = _ := by simp
  have h2 : (∑ i ∈ s \ f, x i) ≤ (s \ f).card * t := by
    calc
      _ ≤ ∑ _i ∈ s \ f, t := by
        apply sum_le_sum
        intro i hi
        obtain ⟨hs, hf⟩ := mem_sdiff.mp hi
        exact le_of_lt (lt_of_not_ge (fun h => hf (mem_filter.mpr ⟨hs, h⟩)))
      _ = _ := by simp
  have hsum := sum_union (f := x) hd
  rw [sdiff_union_of_subset hsub] at hsum
  change (a - t) * s.card ≤ (m - t) * f.card
  calc
    (a - t) * s.card = a * s.card - t * s.card := by ring
    _ ≤ ((s \ f).card : ℝ) * t + f.card * m - t * s.card := by linarith
    _ = (m - t) * f.card := by rw [← hcount]; ring

def printedUpdate (b : ℚ) : ℚ := (7*b - b^2 - 2) / (11*b - 4*b^2 - 3)

def correctedUpdate (b : ℚ) : ℚ := (7*b - 2*b^2 - 2) / (11*b - 4*b^2 - 3)

theorem theorem38_printed_leaves_interval : (701 / 1000 : ℚ) < printedUpdate (2 / 3) := by
  norm_num [printedUpdate]

theorem theorem38_corrected_first_step : correctedUpdate (2 / 3) = 16 / 23 := by
  norm_num [correctedUpdate]

theorem corrected_fixed_point_iff (b : ℚ) (h : 11*b - 4*b^2 - 3 ≠ 0) :
    correctedUpdate b = b ↔ 4*b^3 - 13*b^2 + 10*b - 2 = 0 := by
  rw [correctedUpdate, div_eq_iff h]
  constructor <;> intro he <;> linarith only [he]

/-- At n=16, ℓ=1, d=4, a=8/11, b=7/10 and x=8, the first and third
printed cases of Lemma 31 overlap and prescribe different slopes. -/
theorem lemma31_printed_intervals_overlap :
    (8 : ℝ) ≤ min 16 (16^(8/5 : ℝ)) ∧
      min (4 : ℝ) (16^(8/5 : ℝ)) ≤ 8 ∧
      (8 : ℝ) ≤ min (16^(14/17 : ℝ)) (4*4^(11/6 : ℝ)) ∧
      1 < (6/11 : ℝ)*2^(17/11 : ℝ) := by
  have hfirst : (16 : ℝ) ≤ 16^(8/5 : ℝ) := by
    conv_lhs => rw [← Real.rpow_one (16 : ℝ)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have he : (8 : ℝ) = 16^(3/4 : ℝ) := by
    symm
    calc
      _ = ((2 : ℝ)^4)^(3/4 : ℝ) := by norm_num
      _ = (2 : ℝ)^((4 : ℝ)*(3/4)) := by
        exact (Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2) 4 (3/4)).symm
      _ = (2 : ℝ)^(3 : ℝ) := by norm_num
      _ = _ := by norm_num
  have h₁ : (8 : ℝ) ≤ 16^(14/17 : ℝ) := by
    rw [he]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have h₀ : (4 : ℝ) ≤ 4^(11/6 : ℝ) := by
    conv_lhs => rw [← Real.rpow_one (4 : ℝ)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have h₂ : (8 : ℝ) ≤ 4 * 4^(11/6 : ℝ) := by linarith only [h₀]
  have h₃ : (2 : ℝ) ≤ 2^(17/11 : ℝ) := by
    conv_lhs => rw [← Real.rpow_one (2 : ℝ)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  exact ⟨le_min (by norm_num) ((by norm_num : (8 : ℝ) ≤ 16).trans hfirst),
    (min_le_left _ _).trans (by norm_num), le_min h₁ h₂, by linarith only [h₃]⟩

/-- The envelope used before the printed derivative formula is linear through x=8
for the parameters of the overlap example. -/
theorem lemma31_overlap_envelope (C x : ℝ) (hx : x ≤ 16) :
    C * min x (min (max 16 (max (16^(8/11 : ℝ)*x^(6/11 : ℝ))
        (max (16^(3/5 : ℝ)*x^(7/10 : ℝ)) x))) 64) = C*x := by
  rw [min_eq_left (le_min (hx.trans (le_max_left _ _)) (hx.trans (by norm_num)))]

end OnlineReachabilityPreservers.SourceAudit
