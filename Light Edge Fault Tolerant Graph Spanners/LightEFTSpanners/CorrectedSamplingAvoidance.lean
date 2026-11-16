import LightEFTSpanners.SamplingRestriction
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Exact Bernoulli sampling at the corrected paper's rate `1/f`.
The finite mass and fault-avoidance probability are derived here, independently
of the earlier `1/(2f)` algorithm. The hypothesis `2 <= f` is essential. -/

namespace LightEFTSpanners.CorrectedSampling
open Finset LightSpanners.FiniteSampling
variable {α : Type*} [DecidableEq α]

/-- Exact probability that the selected set avoids every original fault.
Fault identities outside the sampling universe have no effect. -/
theorem avoiding_mass (U F : Finset α) (p : ℝ) :
    (∑ S∈U.powerset with Disjoint S F, mass U p S) =
      (1-p)^(U∩F).card := by
  have hr := sum_mass_restrict U (U∩F) p
    (fun A => if A=∅ then (1:ℝ) else 0) inter_subset_left
  calc
    _ = ∑ S∈U.powerset, mass U p S*(if S∩(U∩F)=∅ then (1:ℝ) else 0) := by
      rw [sum_filter]
      apply sum_congr rfl
      intro S hS
      have hSU := mem_powerset.mp hS
      have hi : S∩(U∩F)=S∩F := by
        ext a
        simp only [mem_inter]
        constructor
        · rintro ⟨ha,_,haF⟩; exact ⟨ha,haF⟩
        · rintro ⟨ha,haF⟩; exact ⟨ha,hSU ha,haF⟩
      rw [hi]
      by_cases hd : Disjoint S F
      · simp [hd,disjoint_iff_inter_eq_empty.mp hd]
      · have hi' : S∩F≠∅ := fun he => hd (disjoint_iff_inter_eq_empty.mpr he)
        simp [hd,hi']
    _ = ∑ A∈(U∩F).powerset, mass (U∩F) p A*(if A=∅ then (1:ℝ) else 0) := hr
    _ = _ := by simp [mass]

/-- The sharp uniform boundary used by the corrected proof. Concavity of log
compares `1-1/f` with the chord joining `1/2` to `1`; equality holds at f=2. -/
theorem fault_power_lower (f : ℕ) (hf : 2≤f) :
    (1:ℝ)/4 ≤ (1-1/(f:ℝ))^f := by
  have hfR : (2:ℝ)≤f := by exact_mod_cast hf
  have hfpos : (0:ℝ)<f := by linarith
  have ha : 0≤(2:ℝ)/f := by positivity
  have hb : 0≤1-(2:ℝ)/f := by
    have hh : (2:ℝ)/f≤1 := (div_le_one hfpos).mpr hfR
    linarith
  have hc := strictConcaveOn_log_Ioi.concaveOn.2
    (by norm_num : (1/2:ℝ)∈Set.Ioi 0) (by norm_num : (1:ℝ)∈Set.Ioi 0)
    ha hb (by ring : (2:ℝ)/f+(1-2/(f:ℝ))=1)
  simp only [smul_eq_mul,Real.log_one,mul_zero,add_zero] at hc
  have harg : (2/(f:ℝ))*(1/2)+(1-2/(f:ℝ))*1=1-1/(f:ℝ) := by ring
  rw [harg] at hc
  have hm := mul_le_mul_of_nonneg_left hc hfpos.le
  have heq : (f:ℝ)*(2/(f:ℝ)*Real.log (1/2))=2*Real.log (1/2) := by
    field_simp
  rw [heq] at hm
  have hp : (0:ℝ)<1-1/(f:ℝ) := by
    have hh : 1/(f:ℝ)≤1/2 := (div_le_div_iff₀ hfpos (by norm_num)).mpr (by linarith)
    linarith
  apply (Real.log_le_log_iff (by norm_num : (0:ℝ)<1/4) (pow_pos hp f)).mp
  calc
    Real.log ((1:ℝ)/4) = 2*Real.log (1/2) := by
      convert Real.log_pow (1/2:ℝ) 2 using 1; norm_num
    _ ≤ (f:ℝ)*Real.log (1-1/(f:ℝ)) := hm
    _ = _ := (Real.log_pow _ _).symm

/-- The corrected sampler omits all at most f original fault identities with
probability at least one quarter, for every f>=2. -/
theorem fault_avoidance (U F : Finset α) (f : ℕ) (hf : 2≤f)
    (hF : F.card≤f) :
    (1:ℝ)/4 ≤ ∑ S∈U.powerset with Disjoint S F, mass U (1/(f:ℝ)) S := by
  have hfR : (1:ℝ)≤f := by exact_mod_cast (show 1≤f by omega)
  have hfpos : (0:ℝ)<f := by linarith
  have hp1 : 1/(f:ℝ)≤1 := (div_le_one hfpos).mpr hfR
  have hcap : (U∩F).card≤f := (card_le_card inter_subset_right).trans hF
  calc
    (1:ℝ)/4 ≤ (1-1/(f:ℝ))^f := fault_power_lower f hf
    _ ≤ (1-1/(f:ℝ))^(U∩F).card :=
      pow_le_pow_of_le_one (by linarith) (sub_le_self _ (by positivity)) hcap
    _ = _ := (avoiding_mass U F (1/(f:ℝ))).symm

theorem accepts_required_edge {actual estimate : ℝ}
    (hactual : 1/4≤actual) (herror : |estimate-actual|≤1/16) :
    1/8≤estimate := by
  have h := (abs_le.mp herror).1
  linarith

theorem accepted_edge_probability {actual estimate : ℝ}
    (haccept : 1/8≤estimate) (herror : |estimate-actual|≤1/16) :
    1/16≤actual := by
  have h := (abs_le.mp herror).2
  linarith

end LightEFTSpanners.CorrectedSampling
