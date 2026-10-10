import LightEFTSpanners.BlockerSampling
import Mathlib.Data.Finset.Max

namespace LightEFTSpanners.BlockerSampling
open Finset LightSpanners.FiniteSampling
variable {α : Type*} [DecidableEq α]

/-- Exactly the candidates selected without a selected relevant blocker. -/
noncomputable def surviving (U : Finset α) (B : α → Finset α) (S : Finset α) : Finset α :=
  U.filter (fun e => e ∈ S ∧ Disjoint (B e ∩ U) S)

/-- Finite linearity for the actual blocker-deletion rule, with no probabilistic
independence or expected-weight law assumed as a hypothesis. -/
theorem expected_surviving_weight (U : Finset α) (B : α → Finset α)
    (p : ℝ) (w : α → ℝ) :
    (∑ S ∈ U.powerset, mass U p S * ∑ e ∈ surviving U B S, w e) =
      ∑ e ∈ U, (∑ S ∈ U.powerset with e∈S ∧ Disjoint (B e ∩ U) S, mass U p S) * w e := by
  classical
  simp only [surviving,sum_filter,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro e he
  rw [sum_mul]
  apply sum_congr rfl
  intro S hS
  split_ifs <;> ring

/-- Corrected Lemma27 weight estimate, on the non-seed candidate edges only.
Keeping this weight separate avoids subtracting the seed-tree baseline. -/
theorem corrected_expected_weight (U : Finset α) (B : α → Finset α)
    (w : α → ℝ) (hw : ∀ e∈U,0≤w e) (f : ℕ) (hf : 0<f)
    (hcap : ∀ e∈U,(B e).card≤f) (hself : ∀ e∈U,e∉B e) :
    (∑ e∈U,w e)/(4*(f:ℝ)) ≤
      ∑ S∈U.powerset,mass U (1/(2*(f:ℝ))) S * ∑ e∈surviving U B S,w e := by
  rw [expected_surviving_weight,sum_div]
  apply sum_le_sum
  intro e he
  have h := corrected_survival U (B e ∩ U) f hf he inter_subset_right
    (fun hx => hself e he (mem_inter.mp hx).1)
    ((card_le_card inter_subset_left).trans (hcap e he))
  have hh := mul_le_mul_of_nonneg_right h (hw e he)
  simpa [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using hh

/-- An actual finite sample achieves the bound; the witness is obtained from
a maximum over the explicit finite sample space. -/
theorem exists_heavy_surviving_sample (U : Finset α) (B : α → Finset α)
    (w : α → ℝ) (hw : ∀ e∈U,0≤w e) (f : ℕ) (hf : 0<f)
    (hcap : ∀ e∈U,(B e).card≤f) (hself : ∀ e∈U,e∉B e) :
    ∃ S ⊆ U, (∑ e∈U,w e)/(4*(f:ℝ)) ≤ ∑ e∈surviving U B S,w e := by
  classical
  obtain ⟨S,hS,hmax⟩ := exists_max_image U.powerset
    (fun S => ∑ e∈surviving U B S,w e) ⟨∅,mem_powerset.mpr (empty_subset _)⟩
  refine ⟨S,mem_powerset.mp hS,?_⟩
  have hfR : (0:ℝ)<f := by exact_mod_cast hf
  have hf1 : (1:ℝ)≤f := by exact_mod_cast hf
  have hp1 : 1/(2*(f:ℝ)) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  calc
    _ ≤ ∑ A∈U.powerset,mass U (1/(2*(f:ℝ))) A *
        ∑ e∈surviving U B A,w e := corrected_expected_weight U B w hw f hf hcap hself
    _ ≤ ∑ A∈U.powerset,mass U (1/(2*(f:ℝ))) A *
        ∑ e∈surviving U B S,w e := by
      apply sum_le_sum
      intro A hA
      exact mul_le_mul_of_nonneg_left (hmax A hA) (mass_nonneg U A (by positivity) hp1)
    _ = _ := by rw [← sum_mul,sum_mass,one_mul]
end LightEFTSpanners.BlockerSampling
