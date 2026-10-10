import LightSpanners.FiniteSampling
import Mathlib.Tactic

/-! Uniform finite Bernoulli sampling for the corrected f=1 boundary.
Probabilities are explicit sums over the powerset, not an assumed oracle law. -/
namespace LightEFTSpanners.BlockerSampling
open Finset LightSpanners.FiniteSampling
variable {α : Type*} [DecidableEq α]

/-- Exact simultaneous-inclusion probability for two distinct elements. -/
theorem pair_probability (U : Finset α) (p : ℝ) {e d : α}
    (he : e ∈ U) (hd : d ∈ U) (hne : e ≠ d) :
    (∑ S ∈ U.powerset with e ∈ S ∧ d ∈ S, mass U p S) = p^2 := by
  have hsub : ({e,d} : Finset α) ⊆ U := insert_subset he (singleton_subset_iff.mpr hd)
  simpa [insert_subset_iff, singleton_subset_iff, hne] using
    sum_mass_containing U {e,d} p hsub

/-- A union bound with the candidate edge conditioned in. The diagonal exclusion
is essential: a self-block would destroy every surviving candidate. -/
theorem survival_union_bound (U B : Finset α) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {e : α} (he : e ∈ U) (hB : B ⊆ U) (hne : e ∉ B) :
    p - B.card * p^2 ≤
      ∑ S ∈ U.powerset with e ∈ S ∧ Disjoint B S, mass U p S := by
  have hpoint (S : Finset α) :
      (if e ∈ S then mass U p S else 0) ≤
      (if e ∈ S ∧ Disjoint B S then mass U p S else 0) +
        ∑ d ∈ B, if e ∈ S ∧ d ∈ S then mass U p S else 0 := by
    have hm := mass_nonneg U S hp0 hp1
    by_cases heS : e ∈ S
    · by_cases hdis : Disjoint B S
      · simp only [heS, hdis, and_self, ite_true]
        exact le_add_of_nonneg_right (sum_nonneg (fun _ _ => by split_ifs <;> positivity))
      · obtain ⟨d,hdB,hdS⟩ := not_disjoint_iff.mp hdis
        simp only [heS, true_and, hdis, ite_false, ite_true, zero_add]
        exact (by simpa [hdS] using
          (single_le_sum (f := fun d => if d ∈ S then mass U p S else 0)
            (fun d _ => by split_ifs <;> positivity) hdB :
            (if d ∈ S then mass U p S else 0) ≤ ∑ d ∈ B, if d ∈ S then mass U p S else 0))
    · simp [heS]
  have hh := sum_le_sum (fun S (_ : S ∈ U.powerset) => hpoint S)
  rw [sum_add_distrib, sum_comm] at hh
  have hleft : (∑ S ∈ U.powerset, if e ∈ S then mass U p S else 0) = p := by
    rw [← sum_filter, sum_mass_mem U p he]
  have hright : (∑ d ∈ B, ∑ S ∈ U.powerset,
      if e ∈ S ∧ d ∈ S then mass U p S else 0) = B.card * p^2 := by
    calc
      _ = ∑ _d ∈ B, p^2 := by
        apply sum_congr rfl
        intro d hd
        rw [← sum_filter, pair_probability U p he (hB hd) (by intro h; exact hne (h ▸ hd))]
      _ = _ := by simp
  rw [hleft, hright, ← sum_filter] at hh
  linarith

/-- Corrected sampling p=1/(2f) gives survival at least 1/(4f), including f=1. -/
theorem corrected_survival (U B : Finset α) (f : ℕ) (hf : 0 < f)
    {e : α} (he : e ∈ U) (hB : B ⊆ U) (hne : e ∉ B) (hcap : B.card ≤ f) :
    1 / (4 * (f : ℝ)) ≤ ∑ S ∈ U.powerset with e ∈ S ∧ Disjoint B S,
      mass U (1 / (2 * (f : ℝ))) S := by
  have hfR : 0 < (f : ℝ) := by exact_mod_cast hf
  have hfone : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hp0 : 0 ≤ 1 / (2 * (f : ℝ)) := by positivity
  have hp1 : 1 / (2 * (f : ℝ)) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    linarith
  have hh := survival_union_bound U B hp0 hp1 he hB hne
  have hb : (B.card : ℝ) ≤ f := by exact_mod_cast hcap
  have hmul := mul_le_mul_of_nonneg_right hb (sq_nonneg (1 / (2 * (f : ℝ))))
  have heq : 1 / (2 * (f : ℝ)) - (f : ℝ) * (1 / (2 * (f : ℝ)))^2 =
      1 / (4 * (f : ℝ)) := by field_simp; ring
  linarith

/-- The source's uncorrected lower probability fails at its allowed boundary. -/
theorem original_probability_at_one : (1 - 1 / (1 : ℝ))^(1 : ℕ) = 0 := by norm_num

/-- Consistent estimates/acceptance thresholds for repaired Algorithms 2 and 3. -/
theorem accepts_required_edge {actual estimate : ℝ}
    (hactual : 1/2 ≤ actual) (herror : |estimate - actual| ≤ 1/8) : 3/8 ≤ estimate := by
  have h := (abs_le.mp herror).1
  linarith

theorem accepted_edge_probability {actual estimate : ℝ}
    (haccept : 3/8 ≤ estimate) (herror : |estimate - actual| ≤ 1/8) : 1/4 ≤ actual := by
  have h := (abs_le.mp herror).2
  linarith

end LightEFTSpanners.BlockerSampling
