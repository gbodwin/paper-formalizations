import LightEFTSpanners.BlockerSampling

namespace LightEFTSpanners.BlockerSampling
open Finset LightSpanners.FiniteSampling
variable {α : Type*} [DecidableEq α]

/-- Exact finite Bernoulli sampling avoids a fault set with the union-bound
probability. Faults outside the sampled universe are harmless. -/
theorem fault_avoidance_union_bound (U F : Finset α) {p : ℝ}
    (hp0 : 0≤p) (hp1 : p≤1) :
    1-F.card*p ≤ ∑ S∈U.powerset with Disjoint S F,mass U p S := by
  have point (S : Finset α) : mass U p S ≤
      (if Disjoint S F then mass U p S else 0)+
        ∑ d∈F,if d∈S then mass U p S else 0 := by
    have hm := mass_nonneg U S hp0 hp1
    by_cases hd : Disjoint S F
    · simp only [hd,ite_true]
      exact le_add_of_nonneg_right (sum_nonneg fun _ _ => by split_ifs <;> positivity)
    · obtain ⟨d,hdS,hdF⟩ := not_disjoint_iff.mp hd
      simp only [hd,ite_false,zero_add]
      exact (by simpa [hdS] using
        (single_le_sum (f:=fun d => if d∈S then mass U p S else 0)
          (fun _ _ => by split_ifs <;> positivity) hdF))
  have hh := sum_le_sum (fun S (_ : S∈U.powerset) => point S)
  rw [sum_mass,sum_add_distrib,sum_comm,←sum_filter] at hh
  have hc : (∑ d∈F,∑ S∈U.powerset,if d∈S then mass U p S else 0)≤F.card*p := by
    calc
      _ ≤ ∑ _d∈F,p := by
        apply sum_le_sum
        intro d _
        by_cases hd : d∈U
        · rw [←sum_filter,sum_mass_mem U p hd]
        · have hz : ∀ S∈U.powerset,d∉S := fun S hS h => hd (mem_powerset.mp hS h)
          simpa only [sum_eq_zero (fun S hS => ite_eq_right (hz S hS))] using hp0
      _ = _ := by simp
  linarith

/-- The required-edge witness survives omission of all at most f faults with
probability at least one half at the repaired rate, also when f=1. -/
theorem corrected_fault_avoidance (U F : Finset α) (f : ℕ) (hf : 0<f)
    (hF : F.card≤f) :
    (1:ℝ)/2 ≤ ∑ S∈U.powerset with Disjoint S F,mass U (1/(2*(f:ℝ))) S := by
  have hfR : (0:ℝ)<f := by exact_mod_cast hf
  have hf1 : (1:ℝ)≤f := by exact_mod_cast hf
  have hp1 : 1/(2*(f:ℝ))≤1 := (div_le_one (by positivity)).mpr (by linarith)
  have hh := fault_avoidance_union_bound U F (by positivity) hp1
  have hc : (F.card:ℝ)≤f := by exact_mod_cast hF
  have hm := mul_le_mul_of_nonneg_right hc (by positivity : 0≤1/(2*(f:ℝ)))
  have he : (f:ℝ)*(1/(2*(f:ℝ)))=1/2 := by field_simp
  rw [he] at hm
  linarith
end LightEFTSpanners.BlockerSampling
