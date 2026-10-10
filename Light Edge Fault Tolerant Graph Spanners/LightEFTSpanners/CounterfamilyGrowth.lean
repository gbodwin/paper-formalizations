import LightEFTSpanners.CounterfamilyWeight
import Mathlib.Analysis.Real.Sqrt

namespace LightEFTSpanners.CounterfamilyWeight
open SimpleGraph LightSpanners

/-- No constant times sqrt(n) bounds either actual competitive ratio in this
single graph family. The two optimal denominators exist simultaneously. -/
theorem no_uniform_sqrt_bound (C : ℝ) (hC : 0 ≤ C) :
    ∃ (m : ℕ) (Q₂ Q₃ : SimpleGraph (Fin m ⊕ Fin m)), 4 ≤ m ∧
      IsMinimumFTPreserver (completeBipartiteGraph (Fin m) (Fin m)) Q₂ (fun _ => 1) 2 ∧
      IsMinimumFTPreserver (completeBipartiteGraph (Fin m) (Fin m)) Q₃ (fun _ => 1) 3 ∧
      ∀ H : SimpleGraph (Fin m ⊕ Fin m),
        IsEFTSpanner (completeBipartiteGraph (Fin m) (Fin m)) H (fun _ => 1) (5/2) 1 →
        C * Real.sqrt (2*m) < competitiveLightness H Q₂ (fun _ => 1) ∧
        C * Real.sqrt (2*m) < competitiveLightness H Q₃ (fun _ => 1) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (max (4:ℝ) (16*C))
  have hN4 : 4 < (N:ℝ) := lt_of_le_of_lt (le_max_left _ _) hN
  have hNC : 16*C < (N:ℝ) := lt_of_le_of_lt (le_max_right _ _) hN
  have hNn : 4 ≤ N := by exact_mod_cast hN4.le
  have hNpos : 0 < (N:ℝ) := by linarith
  have hm : 4 ≤ N^2 := by nlinarith
  obtain ⟨Q₂,hQ₂,h₂⟩ := two_fault_counterfamily (N^2) (by omega)
  obtain ⟨Q₃,hQ₃,h₃⟩ := three_fault_counterfamily (N^2) hm
  have hsqrt : Real.sqrt (2*(N^2:ℕ)) ≤ 2*(N:ℝ) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · push_cast
      nlinarith [sq_nonneg (N:ℝ)]
  have hs : C*Real.sqrt (2*(N^2:ℕ)) < ((N^2:ℕ):ℝ)/8 := by
    have hl := mul_le_mul_of_nonneg_left hsqrt hC
    have hx := mul_lt_mul_of_pos_right hNC hNpos
    push_cast at hl ⊢
    nlinarith
  refine ⟨N^2,Q₂,Q₃,hm,hQ₂,hQ₃,fun H hH => ?_⟩
  constructor
  · apply hs.trans_le
    apply le_trans ?_ (h₂ H hH)
    nlinarith [show (0:ℝ) ≤ (N^2:ℕ) by positivity]
  · exact hs.trans_le (h₃ H hH)

end LightEFTSpanners.CounterfamilyWeight
