import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

set_option autoImplicit false

namespace LightSpanners.FiniteSampling

open scoped BigOperators

variable {α : Type*} [DecidableEq α]

/-- The Bernoulli mass of `S`, relative to the finite universe `U`.
The sample space consists of `U.powerset`. -/
noncomputable def mass (U : Finset α) (p : ℝ) (S : Finset α) : ℝ :=
  p ^ S.card * (1 - p) ^ (U \ S).card

/-- Every outcome in the finite sample space has nonnegative mass. -/
theorem mass_nonneg (U S : Finset α) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ mass U p S :=
  mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (sub_nonneg.mpr hp1) _)

/-- The masses sum to one. This polynomial identity does not itself require
`0 ≤ p ≤ 1`; those bounds are needed only for nonnegativity. -/
theorem sum_mass (U : Finset α) (p : ℝ) :
    ∑ S ∈ U.powerset, mass U p S = 1 := by
  have hunit : p + (1 - p) = 1 := by rw [add_comm, sub_add_cancel]
  simpa [mass, hunit] using
    (Finset.prod_add (fun _ : α => p) (fun _ : α => 1 - p) U).symm

/-- The probability that every element of `R` is selected is `p ^ R.card`.
No assumption of the desired sampling identity is used: this follows by expanding
an ordinary finite product, with the excluded choice set to zero on `R`. -/
theorem sum_mass_containing (U R : Finset α) (p : ℝ) (hR : R ⊆ U) :
    ∑ S ∈ U.powerset with R ⊆ S, mass U p S = p ^ R.card := by
  classical
  have hunit : p + (1 - p) = 1 := by rw [add_comm, sub_add_cancel]
  have hlhs : (∏ e ∈ U, (p + if e ∈ R then 0 else 1 - p)) = p ^ R.card := by
    calc
      _ = ∏ e ∈ R, (p + if e ∈ R then 0 else 1 - p) :=
        (Finset.prod_subset hR (by intro e he hn; simp [hn, hunit])).symm
      _ = ∏ _e ∈ R, p := by
        apply Finset.prod_congr rfl
        intro e he
        simp [he]
      _ = p ^ R.card := by simp
  have hrhs :
      (∑ S ∈ U.powerset,
        (∏ _e ∈ S, p) * ∏ e ∈ U \ S, (if e ∈ R then 0 else 1 - p)) =
      ∑ S ∈ U.powerset with R ⊆ S, mass U p S := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro S hS
    by_cases hRS : R ⊆ S
    · rw [ite_eq_left hRS]
      have hc : (∏ e ∈ U \ S, (if e ∈ R then 0 else 1 - p)) =
          ∏ _e ∈ U \ S, (1 - p) := by
        refine Finset.prod_congr rfl ?_
        intro e he
        exact ite_eq_right (fun her => (Finset.mem_sdiff.mp he).2 (hRS her))
      simp [hc, mass]
    · rw [ite_eq_right hRS]
      obtain ⟨e, heR, heS⟩ := Finset.not_subset.mp hRS
      have hz : (∏ e ∈ U \ S, (if e ∈ R then (0 : ℝ) else 1 - p)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_sdiff.mpr ⟨hR heR, heS⟩) (ite_eq_left heR)
      rw [hz, mul_zero]
  rw [← hrhs, ← Finset.prod_add]
  exact hlhs

/-- A specified element of the universe is selected with probability `p`. -/
theorem sum_mass_mem (U : Finset α) (p : ℝ) {e : α} (he : e ∈ U) :
    ∑ S ∈ U.powerset with e ∈ S, mass U p S = p := by
  simpa using sum_mass_containing U {e} p (Finset.singleton_subset_iff.mpr he)

/-- Linearity of the finite Bernoulli expectation, for arbitrary real weights.
In particular, weights need not be nonnegative. -/
theorem expected_sum (U : Finset α) (p : ℝ) (w : α → ℝ) :
    ∑ S ∈ U.powerset, mass U p S * (∑ e ∈ S, w e) =
      p * ∑ e ∈ U, w e := by
  classical
  calc
    _ = ∑ S ∈ U.powerset, ∑ e ∈ U, if e ∈ S then mass U p S * w e else 0 := by
      refine Finset.sum_congr rfl ?_
      intro S hS
      rw [Finset.mul_sum]
      calc
        _ = ∑ e ∈ S, if e ∈ S then mass U p S * w e else 0 := by simp
        _ = ∑ e ∈ U, if e ∈ S then mass U p S * w e else 0 :=
          Finset.sum_subset (Finset.mem_powerset.mp hS)
            (by intro e he hn; simp [hn])
    _ = ∑ e ∈ U, ∑ S ∈ U.powerset, if e ∈ S then mass U p S * w e else 0 :=
      Finset.sum_comm
    _ = ∑ e ∈ U, (∑ S ∈ U.powerset with e ∈ S, mass U p S) * w e := by
      refine Finset.sum_congr rfl ?_
      intro e he
      rw [Finset.sum_filter, Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro S hS
      by_cases heS : e ∈ S <;> simp [heS]
    _ = ∑ e ∈ U, p * w e := by
      refine Finset.sum_congr rfl ?_
      intro e he
      rw [sum_mass_mem U p he]
    _ = p * ∑ e ∈ U, w e := (Finset.mul_sum U w p).symm

end LightSpanners.FiniteSampling
